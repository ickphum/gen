#!/usr/bin/perl -w

# gen.pl
use strict;
my $LINES=0;
my $COLS=0;
use POSIX qw(ceil);
use Time::HiRes qw(usleep);
use Tk;
use Tk::PNG;
use Tk::ROText;
use File::Basename;
use Getopt::Std;

my %args;
my $breed_speed = 2; # breeding occurs every $breed_speed loops, so 1 is max.
my $logfile = "gen.log";
my $stdout_fh;
my $gen = 0;
my $next_id = 0;
my $gen_id_counter;
my $stop_flag = 0;
my $spin = 0;
my $debug = 0;
my $refresh = 1;
my $stop_after_gen = 0;
my $debug_after_gen = 0;
# key is item type, val is listref to items
my %tree;
# key is item id, val is listref to resonances
my %item_res;
# key is item id, val is listref to items
my %prev_joining_list;
# key is item id, val is item ref
my %active_item;
# key is item id; val is list ref to list of rect refs
my %item_exclude;
my $GY=70;
my $GX=70;
# tk variables
my $main_win;
my $td_canvas;
# keyed by color name
my %small_img;
my %td_img;
my %roof_img;
my %roof_corner_img;
my $id_to_inspect = 0;

my $image_x_offset = 6;
my $image_y_offset = 3;
my $image_z_offset = 5;

# types of objects
my $CELL = 0x01;
my $WALL = 0x02;
my $ROOF = 0x04;
my $PEDIMENT = 0x08;
my $RES = 0x10;
my $ROOM = 0x20;
my $BUILDING = 0x40;
my $COLUMN = 0x80;
my $MAP_WALL = 0x100;
my $RESKEY_THING = 0x200;

# type group masks
my $WALL_GROUP = $WALL | $ROOF | $PEDIMENT;
my $MAP_GROUP = $COLUMN | $MAP_WALL;
my $RESKEY_GROUP = $RESKEY_THING;

# states of objects
my $SEEK = 0x01;
my $BUILD = 0x02;
my $COMPLETING = 0x04;
my $WAITING = 0x08;
my $DEAD = 0x10;
my $FINISHED = 0x20;
my $JOIN = 0x40;

# state group masks
my $SEEKING_GROUP = $SEEK | $JOIN;

# creation flags
my $FL_ACTIVE=0x01;
my $FL_RESONATE=0x02;

# cell images based on state
my %state_color = (
	$SEEK => "red", # not used; seek_color list used instead
	$BUILD => "orange",
	$COMPLETING => "yellow",
	$WAITING => "redbrick",
	);

# cell images based on age (when in seek state)
my %seek_color = (
	0 => "red",
	1 => "orange",
	2 => "yellow",
	3 => "green",
	4 => "blue",
	5 => "violet",
	);

# object lifespan
my %lifespan = (
	$CELL => 100,
	$WALL => 50,
	$ROOM => 3000, # this is modified by room size
	);

# directions
my $NORTH = 0;
my $EAST = 1;
my $SOUTH = 2;
my $WEST = 3;

# gable statuses; these are bitmap values
my $GS_NONE = 0;
my $GS_START = 1;
my $GS_END = 2;

# map building grid size to a column size; the 0 entry is there so
# we can always subtract 2 from the real grid size and still find
# an entry
my %column_size = (
	10 => 3,
	8 => 3,
	6 => 3,
	4 => 2,
	2 => 1,
	0 => 1,
	);

# maps for each column size
my %column_res_map = (
	1 => [ [0,0] ],
	2 => [ [1,0], [0,1], [-1,0], [0,-1] ],
	3 => [ [-1,-1], [0,-1], [1,-1], [1,0], 
			[1,1], [0,1], [-1,1], [-1,0] ],
	);

# minimum wall segment lengths for each column size
my %column_wall_min = (
	1 => 2,
	2 => 4,
	3 => 6,
	);

# column positions
my $CP_WALL = 1;
my $CP_OUTSIDE_CORNER = 2;
my $CP_INSIDE_CORNER = 3;

sub
done 
{ 
	print "@_\n";
	exit;
}

sub
numeric 
{
	$a <=> $b;
}
sub
rev_numeric 
{
	$b <=> $a;
}

sub
min(@) 
{ 
	my $min = undef;
	foreach (@_) {
		$min = $_ if !defined($min) || $_ < $min;
	}
	return $min;
}

sub
max(@) 
{ 
	my $max = undef;
	foreach (@_) {
		$max = $_ if !defined($max) || $_ > $max;
	}
	return $max;
}

# proto for recursion
sub copy($;$);
sub
copy($;$)
{

	my ($ref, $copied_refs) = @_;
	my $new_ref;

	# make a deep copy of a data structure, expanding hashes or lists

	# if we didn't get a $copied_refs value, this must be the top level so
	# we should create it. This hash tracks all the refs (lists or hashes)
	# we've expanded to prevent infinite loops on recursive data structures.
	unless ($copied_refs) {
		$copied_refs = { };
	}

	if (my $reftype = ref $ref) {
		if ($reftype eq 'ARRAY') {
			# if we've seen this list before, bail to prevent looping
			return $$copied_refs{$ref} if $$copied_refs{$ref};

			# if we get asked to copy this list again, the copy we're making
			# now will be returned
			$$copied_refs{$ref} = $new_ref = [];

			#copy
			foreach my $index (0 .. $#$ref) {
				push @$new_ref, copy($$ref[$index], $copied_refs);
			}
		}
		elsif ($reftype eq 'HASH') {
			# if we've seen this hash before, bail to prevent looping
			return $$copied_refs{$ref} if $$copied_refs{$ref};

			# if we get asked to copy this hash again, the copy we're making
			# now will be returned
			$$copied_refs{$ref} = $new_ref = {};

			# copy
			foreach my $key (keys %$ref) {
				$$new_ref{$key} = copy($$ref{$key}, $copied_refs);
			}
		}
		elsif ($reftype eq 'SCALAR') {
			# create a new copy of this scalar 
			my $new_value = $$ref;
			# and return a ref to the new copy
			$new_ref = \$new_value;
		}
		else {
			# anything else gets returned without being copied,
			# the assumption being we won't be changing the object
			# being referred to (subroutine, filehandle, ?) and
			# and so having a shared ref to it won't cause us grief
			$new_ref = $ref;
		}
	}
	else {
		# not a ref, just return the value
		$new_ref = $ref;
	}

	return $new_ref;

}

sub
get_direction($$) 
{
	my ($start, $end) = @_;
	my $dir = undef;

	my $delta_x = $$start[0] - $$end[0];
	my $delta_y = $$start[1] - $$end[1];
	print "get_direction dx = $delta_x, dy = $delta_y\n" if $debug;
	if ($delta_x * $delta_y) {
		die "Angled line ?; from $$start[0],$$start[1] to $$end[0],$$end[1], dx = $delta_x, dy = $delta_y\n";
	}
	elsif ($delta_x > 0) { $dir = $WEST; }
	elsif ($delta_x < 0) { $dir = $EAST; }
	elsif ($delta_y > 0) { $dir = $NORTH; }
	elsif ($delta_y < 0) { $dir = $SOUTH; }

	# will return undef for matching points
	return $dir;
}

sub
spin_resmap($$)
{
	my ($facing, $resmap) = @_;
#	my $debug = 1;

	# spin the points around 0,0 according to the column_facing.
	# We could work out the matrix for each amount of spin (90, 180, 270)
	# but it's easier to just spin 90 as many times as we need.
	print "original facing = $facing\n" if $debug;
	while ($facing--) {
		print "spin resses 90 clockwise\n" if $debug;
		for my $rm (0 .. $#$resmap) {
			my $res = $$resmap[$rm];
			print "spin res $rm from $$res[0], $$res[1]" if $debug;
			my $next_x = - $$res[1];
			my $next_y = $$res[0];
			$$res[0] = $next_x;
			$$res[1] = $next_y;
			print " to $$res[0], $$res[1]\n" if $debug;
			if (defined(my $attribs = $$res[2])) {
				# we have a roof tile so we rotate accordingly
				print "Rotate roof from $$attribs{shape}" if $debug;
				$$attribs{shape} =~ s/(.+_roof_)(.{6})(.{2})/$1$3$2/;
				print " to $$attribs{shape}\n" if $debug;
			}
		}
	}
}

sub 
size_1_buttress_resmap
{
	my $thing = shift;
	my $column = $$thing{column} or die "buttress has no column";
#	my $debug = 1;

	# check if we've calculated the map for this before
	if (defined ($$thing{cache_layer}) && $$thing{cache_layer} == $$thing{layer}) {
		return $$thing{cached_map};
	}

	print "size_1_buttress_resmap, layer $$thing{layer}\n" if $debug;

	if ($$thing{layer} == 0) {
		# first layer; do initial tasks
		$$thing{buttress_height} = int($$column{final_height} / 3);
	}

	# have we finished?
	if ($$thing{layer} > $$thing{buttress_height}) {
		print "No more points in size_1_buttress_resmap\n" if $debug;
		return undef;
	}

	# this routine will return this list reference
	my $resmap = [];

	# create the default resmap (assume column_facing == 0)
	if ($$column{column_position} == $CP_WALL) {
		if ($$thing{layer} < $$thing{buttress_height}) {
			push @$resmap, [ -1, 0 ];
		}
		else {
			push @$resmap, [ -1, 0, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ];
		}
	}
	elsif ($$column{column_position} == $CP_OUTSIDE_CORNER) {
		if ($$thing{layer} < $$thing{buttress_height}) {
			push @$resmap, [ 0, 1 ];
			push @$resmap, [ -1, 0 ];
		}
		else {
			# final layer; slopes
			push @$resmap, [ 0, 1, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LMHHHMLL" } ];
			push @$resmap, [ -1, 0, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ];
		}
	}
	elsif ($$column{column_position} == $CP_INSIDE_CORNER) {
		print "No inside corner buttress for size_1_buttress_resmap\n" if $debug;
		return undef;
	}
	else {
		die "Illegal column position $$column{column_position}";
	}

	# spin the points around 0,0 according to the column_facing.
	spin_resmap($$column{facing}, $resmap);

	if ($debug) {
		foreach my $res (@$resmap) {
			my ($x, $y, $attribs) = @$res;
			print "$x,$y";
			print " shape $$attribs{shape}" if defined($attribs);
			print "\n";
		}
	}

	# cache this map
	$$thing{cached_map} = $resmap;
	$$thing{cache_layer} = $$thing{layer};

	return $resmap;

}

sub 
size_2_buttress_resmap
{
	my $thing = shift;
	my $column = $$thing{column} or die "buttress has no column";

	# check if we've calculated the map for this before
	if (defined ($$thing{cache_layer}) && $$thing{cache_layer} == $$thing{layer}) {
		return $$thing{cached_map};
	}

	print "size_2_buttress_resmap, layer $$thing{layer}\n" if $debug;

	if ($$thing{layer} == 0) {
		# first layer; do initial tasks
		$$thing{buttress_height} = $$column{final_height} >> 1;
	}

	# have we finished?
	if ($$thing{layer} > $$thing{buttress_height}) {
		print "No more points in size_2_buttress_resmap\n" if $debug;
		return undef;
	}

	# this routine will return this list reference
	my $resmap = [];

	# create the default resmap (assume column_facing == 0)
	if ($$column{column_position} == $CP_WALL) {
		if ($$thing{layer} < $$thing{buttress_height}) {
			push @$resmap, [ -2, 0 ];
		}
		else {
			push @$resmap, [ -2, 0, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ];
		}
	}
	elsif ($$column{column_position} == $CP_OUTSIDE_CORNER) {
		if ($$thing{layer} < $$thing{buttress_height}) {
			push @$resmap, [ 0, 2 ];
			push @$resmap, [ -2, 0 ];
		}
		else {
			# final layer; slopes
			push @$resmap, [ 0, 2, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LMHHHMLL" } ];
			push @$resmap, [ -2, 0, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ];
		}
	}
	elsif ($$column{column_position} == $CP_INSIDE_CORNER) {
		print "No inside corner buttress for size_2_buttress_resmap\n" if $debug;
		return undef;
	}
	else {
		die "Illegal column position $$column{column_position}";
	}

	# spin the points around 0,0 according to the column_facing.
	spin_resmap($$column{facing}, $resmap);

	if ($debug) {
		foreach my $res (@$resmap) {
			my ($x, $y, $attribs) = @$res;
			print "$x,$y";
			print " shape $$attribs{shape}" if defined($attribs);
			print "\n";
		}
	}

	# cache this map
	$$thing{cached_map} = $resmap;
	$$thing{cache_layer} = $$thing{layer};

	return $resmap;

}

sub 
size_3_buttress_resmap
{
	my $thing = shift;
	my $column = $$thing{column} or die "buttress has no column";

	# check if we've calculated the map for this before
	if (defined ($$thing{cache_layer}) && $$thing{cache_layer} == $$thing{layer}) {
		return $$thing{cached_map};
	}

	print "size_3_buttress_resmap, layer $$thing{layer}\n" if $debug;

	if ($$thing{layer} == 0) {
		# first layer; do initial tasks
		$$thing{first_step_height} = int($$column{final_height} / 3);
		$$thing{second_step_height} = $$thing{first_step_height} * 2;
		$$thing{third_step_height} = $$column{final_height} - 1;
	}

	# have we finished?
	if ($$thing{layer} > $$thing{third_step_height}) {
		print "No more points in size_3_buttress_resmap\n" if $debug;
		return undef;
	}

	# this routine will return this list reference
	my $resmap = [];

	# create the default resmap (assume column_facing == 0)

	# create the side we need for both wall and outside corner, then
	# duplicate and spin it if outside corner
	if ($$column{column_position} == $CP_WALL || $$column{column_position} == $CP_OUTSIDE_CORNER) {
		if ($$thing{layer} < ($$thing{first_step_height} - 1)) {
			push @$resmap, ( [ -3,-1 ], [ -3,1 ] ) ;
		}
		elsif ($$thing{layer} < $$thing{first_step_height}) {
			push @$resmap, ( [ -3,-1 ], [ -3,1 ], [ -2,-1 ], [ -2,0 ], [ -2,1 ] ) ;
		}
		elsif ($$thing{layer} == $$thing{first_step_height}) {
			push @$resmap, ( [ -2,-1 ], [ -2,0 ], [ -2,1 ] ) ;
			push @$resmap, (
				[ -3,-1, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ],
				[ -3,1, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ],
				) ;
		}
		elsif ($$thing{layer} < $$thing{second_step_height}) {
			push @$resmap, ( [ -2,-1 ], [ -2,0 ], [ -2,1 ] ) ;
		}
		elsif ($$thing{layer} == $$thing{second_step_height}) {
			push @$resmap, (
				[ -2,-1, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ],
				[ -2,0 ],
				[ -2,1, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ],
				) ;
		}
		elsif ($$thing{layer} < $$thing{third_step_height}) {
			push @$resmap, ( [ -2,0 ] ) ;
		}
		elsif ($$thing{layer} == $$thing{third_step_height}) {
			push @$resmap, [ -2, 0, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLMHHHM" } ];
		}

		if ($$column{column_position} == $CP_OUTSIDE_CORNER) {
			# deep copy of resmap
			my $dup_resmap = copy($resmap);

			# spin the copy so it's positioned correctly
			spin_resmap(3, $dup_resmap);

			# add the copied map to resmap
			push @$resmap, ( @$dup_resmap );
		}
	}
	elsif ($$column{column_position} == $CP_INSIDE_CORNER) {
		print "No inside corner buttress for size_3_buttress_resmap\n" if $debug;
		return undef;
	}
	else {
		die "Illegal column position $$column{column_position}";
	}

	# spin the points around 0,0 according to the column_facing.
	spin_resmap($$column{facing}, $resmap);

	if ($debug) {
		foreach my $res (@$resmap) {
			my ($x, $y, $attribs) = @$res;
			print "$x,$y";
			print " shape $$attribs{shape}" if defined($attribs);
			print "\n";
		}
	}

	# cache this map
	$$thing{cached_map} = $resmap;
	$$thing{cache_layer} = $$thing{layer};

	return $resmap;

}

sub
resize_points(@) 
{

	my ($resize_factor, $points, $thing) = @_;
	my @new_points;
#	my $debug = 1;
	my @point_gable_status;
	my @new_point_gable_status;
	my $nbr_new_points = 0;

	if ($thing && $$thing{point_gable_status}) {
		# copy these lists for ease of reference; we'll copy the (possibly)
		# amended lists back when we're done.
		@point_gable_status = @{$$thing{point_gable_status}};
		@new_point_gable_status = @{$$thing{point_gable_status}};
	}

	print "resize_points: " if $debug;
	if ($debug) {
		foreach (@$points) {
			printf "(%d,%d) ", @$_;
		}
		print "\n";
	}

	# find the initial previous direction, ie from the last point to the first
	my $prev_dir = get_direction($$points[$#$points], $$points[0]);
	foreach my $p (0 .. $#$points) {
		# direction to the next point
		my $dir = get_direction($$points[$p], $$points[$p == $#$points ? 0 : $p+1]);

		my ($point_delta_x, $point_delta_y);

		if ($point_gable_status[$p]) {
			printf "$p is gable point at (%d,%d) ", @{$$points[$p]} if $debug;
			if ($point_gable_status[$p] & $GS_START) {
				print "start\n" if $debug;
				if ($point_gable_status[$p] & $GS_END) {
					print "and end\n" if $debug;
					# both a start and an end; we need to add a new point which will be the new end,
					# and a normal point in between the end and the start

					# reverse the logic to find the new end
					$point_delta_x = $dir % 2 ? 0 : ($dir == $NORTH || $prev_dir == $NORTH ? $resize_factor * -1 : $resize_factor);
					$point_delta_y = $dir % 2 ? ($dir == $EAST || $prev_dir == $EAST ? $resize_factor * -1 : $resize_factor) : 0;

					# create the point
					my $new_point = [ ${$$points[$p]}[0] + $point_delta_x, ${$$points[$p]}[1] + $point_delta_y ];
					printf "new end at (%d,%d) ", @$new_point if $debug;
					push @new_points, $new_point;

					# normal logic to find the intervening point
					$point_delta_x = $dir == $NORTH || $prev_dir == $NORTH ? $resize_factor * -1 : $resize_factor;
					$point_delta_y = $dir == $EAST || $prev_dir == $EAST ? $resize_factor * -1 : $resize_factor;

					# create the point
					$new_point = [ ${$$points[$p]}[0] + $point_delta_x, ${$$points[$p]}[1] + $point_delta_y ];
					printf "new corner at (%d,%d) ", @$new_point if $debug;
					push @new_points, $new_point;

					# replace the start+end with 3 separate entries in the gable status list (we refresh the
					# master list once we've finished)
					splice @new_point_gable_status, $p + $nbr_new_points, 1, ($GS_END, $GS_NONE, $GS_START);
					print "New gs list is ", join(',',@new_point_gable_status), "\n" if $debug;

					# count the new points so we fix the correct part of the gs list for future points
					$nbr_new_points +=2;

				}
				# move the existing point as a start only
				$point_delta_x = $dir % 2 ? ($dir == $NORTH || $prev_dir == $NORTH ? $resize_factor * -1 : $resize_factor) : 0;
				$point_delta_y = $dir % 2 ? 0 : ($dir == $EAST || $prev_dir == $EAST ? $resize_factor * -1 : $resize_factor);
			}
			elsif ($point_gable_status[$p] & $GS_END) {
				print "end only\n" if $debug;
				# move the existing point as an end only
				$point_delta_x = $prev_dir % 2 ? ($dir == $NORTH || $prev_dir == $NORTH ? $resize_factor * -1 : $resize_factor) : 0;
				$point_delta_y = $prev_dir % 2 ? 0 : ($dir == $EAST || $prev_dir == $EAST ? $resize_factor * -1 : $resize_factor);
			}
		}
		else {
			$point_delta_x = $dir == $NORTH || $prev_dir == $NORTH ? $resize_factor * -1 : $resize_factor;
			$point_delta_y = $dir == $EAST || $prev_dir == $EAST ? $resize_factor * -1 : $resize_factor;
		}

		my $new_point = [ ${$$points[$p]}[0] + $point_delta_x, ${$$points[$p]}[1] + $point_delta_y ];
		printf "Resize point at %d,%d, pdir = $prev_dir, dir = $dir, dx = $point_delta_x, dy = $point_delta_y = %d, %d\n",
			@{$$points[$p]}, @$new_point if $debug > 1;
		printf "move point $p to (%d,%d)\n", @$new_point if $debug;

		push @new_points, $new_point;

		# replace
		$prev_dir = $dir;
	}
	print "\n" if $debug;

	# copy the revised lists back to the thing
	if ($thing && $$thing{point_gable_status}) {
		$$thing{point_gable_status} = \@new_point_gable_status;	
	}

	if ($nbr_new_points) {
		# must be a gable map in use
		$$thing{change_points} = find_next_change(\@new_points, $thing);
		# safe_loops is still correct
		shift @{$$thing{change_points}};
		print "Recalc'ed next change after gable splits\n" if $debug;
	}

	@$points = (@new_points);
	if ($debug) {
		print "new_points = ";
		foreach (@$points) {
			printf "(%d,%d) ", @$_;
		}
		print "\n";
	}

}

sub 
find_ends($) 
{

	my $points_ref = shift;
	my @points = @{$points_ref};
#	my $debug = 1;
	my %end;

	print "find_end\n" if $debug;

	# make a copy of the points list so we can change it
	my @points_copy = (@points);
	# add the first 3 points to the end of the list so we can look forward 3 points
	# from each original point
	push @points_copy, @points_copy[0..2];
	# make a list of the directions between each point in the extended list
	my @dir;
	my $nbr_coincident_points = 0;
	for (my $p = 0; $p < $#points_copy; $p++) {
		my $next_dir = get_direction($points_copy[$p], $points_copy[$p+1]);
		# mark coincident points for later treatment
		unless (defined($next_dir)) {
			$next_dir = -1;
			$nbr_coincident_points++;
		}
		push @dir, $next_dir;
		print "dir $p = $dir[$#dir]\n" if $debug;
	}

	# fix the coincident points now we have the full list of directions
	while ($nbr_coincident_points) {
		for (my $d = 0; $d <= $#dir; $d++) {
			if ($dir[$d] == -1) {
				print "Coincident points at $d\n" if $debug;
				# assume the direction is +1 from prev
				my $prev_dir = $d > 0 ? $dir[$d-1] : $dir[$#dir];
				# this shouldn't happen - gable map won't degrade to a single point
				# and single point doesn't need to call find_ends after finishing the
				# last (2nd-last?) level
				die "Multiple coincident points" if $prev_dir == -1;
				$dir[$d] = ($prev_dir + 1) % 4;
				$nbr_coincident_points--;
			}
		}
	}

	# A* doesn't work here for some reason
	my $dir_str = pack "A" x ($#dir+1), @dir;
	print "dir_str = $dir_str\n" if $debug;

	for (my $p = 0; $p <= $#points; $p++) {
		# ascending directions mean a convex end
		if ($dir_str =~ /^(012|123|230|301)/) {
			my $width = abs(($points_copy[$p+1][0] - $points_copy[$p+2][0]) +
				($points_copy[$p+1][1] - $points_copy[$p+2][1]));
			$end{$width} = [] unless $end{$width};
			push @{$end{$width}}, $p;
			print "End at $p, width $width\n" if $debug,
		}
		substr $dir_str, 0, 1, "";
	}

	return \%end;

}

sub 
find_next_change($;$) 
{

	my $points = shift;
	my $thing = shift;
#	my $debug = 1;
	my $end;

	print "find_next_change on $#$points+1 points\n" if $debug;

	# get a hashref with keys of end widths and values of listrefs containing point indexes
	$end = find_ends($points);

	# if we have a thing reference and the thing knows about gable statuses,
	# adjust the widths to take into account the differing rates of decrease
	# for gable corners. It's easier to build a new hash than adjust the existing one.
	if ($thing && $$thing{point_gable_status}) {
		my $new_end = {};
		my $point_gable_status = $$thing{point_gable_status};
		print "check for gables affecting widths: gs = [ @$point_gable_status ]\n" if $debug;
		foreach (keys %$end) {
			print "gable check width = $_\n" if $debug;
			foreach my $p (@{$$end{$_}}) {
				my $new_width = $_;
				# we only care about the 2nd and 3rd points in the corner
				my $second = ($p+1) % ($#$points+1);
				my $third = ($p+2) % ($#$points+1);
				print "p = $p, 2nd = $second, 3rd = $third\n" if $debug;
				# note that we're looking for exact matches on the gable statuses;
				# points that are both starts and ends will shrink normally.
				if ($$point_gable_status[$second] == $GS_END && $$point_gable_status[$third] == $GS_START) {
					# this end lies between two gable ends but isn't a gable itself;
					# the end won't get smaller at all as we resize, so don't add it to the 
					# hash of ends for consideration
					print "p between gables, skip\n" if $debug;
					$new_width = 0;
				}
				elsif ($$point_gable_status[$second] == $GS_END || $$point_gable_status[$third] == $GS_START) {
					# this end adjoins a gable end, so will last twice as long as we thought
					$new_width = $_ * 2;
					print "p next to one gable, new width = $new_width\n" if $debug;
				}
				else {
					print "p not near 1 gable, width unchanged\n" if $debug;
				}
				# add this end to the new hash if appropriate
				if ($new_width) {
					print "Adding $p to width $new_width\n" if $debug;
					$$new_end{$new_width} ||= [];
					push @{$$new_end{$new_width}}, $p;
				}
			}
		}
		$end = $new_end;
	}

	# create (and return a ref to) a list of the ends (ie index of first point in end) with the smallest width
	my @change_points;
	foreach (sort { $a <=> $b } keys %$end) {
		print "width = $_\n" if $debug;
		# add the width of the end (halved) as the first element of the list; this will
		# be shifted off and used as the "safe_loops" value, ie we can simply
		# resize for this many before we need to prune_points() and find_next_change() again.
		push @change_points, int($_/2);
		foreach my $p (@{$$end{$_}}) {
			print "p = $p\n" if $debug;
			push @change_points, $p;
		}
		last;
	}


	return \@change_points;
}

sub 
find_gable_statuses($) 
{

	my $thing = shift;
	my $debug = 1;
	my $end;

	print "find_gable_statuses\n" if $debug;

	my @base_points = @{$$thing{base_points}};

	# get a hashref with keys of end widths and values of listrefs containing point indexes
	$end = find_ends(\@base_points);

	# create a list of all the end points
	my @end_points;
	my @widths = sort {$b <=> $a } keys %$end;
	my $nbr_skips = $#widths > 1 ? $#widths - 1 : 0;
	foreach (@widths) {
		print "end width $_, skip = $nbr_skips\n" if $debug;
		$nbr_skips-- and next if $nbr_skips;
		# informal width limit, to stop the long side of buildings being gables
#		next if $_ > 40;
		foreach my $g (@{$$end{$_}}) {
			print "gable point g = $g\n" if $debug;
			push @end_points, $g;
		}
	}

	# initialise all points' gable status to 0
	my $gable_status = [ map (0,0..$#base_points) ];

	# mark all gable starts and ends; they can coincide, hence the bitmap
	foreach my $g (sort {$a <=> $b} @end_points) {
		my $start_point = ($g + 1) % ($#base_points+1);
		my $end_point = ($g + 2) % ($#base_points+1);
		print "Start of end = $g, gable points = $start_point, $end_point\n" if $debug;
		if ($$gable_status[$start_point] & $GS_END && $$thing{no_shared_gables}) {
			print "Skip 1 (no shared)\n" if $debug;
			next;
		}
		if ($$gable_status[$end_point] & $GS_START && $$thing{no_shared_gables}) {
			print "Skip 2 (no shared)\n" if $debug;
			next;
		}
		$$gable_status[$start_point] |= $GS_START;
		print "Status at 1st gable point $start_point |= START, now $$gable_status[$start_point]\n" if $debug;
		$$gable_status[$end_point] |= $GS_END;
		print "Status at 2nd gable point $end_point |= END, now $$gable_status[$end_point]\n" if $debug;
	}

	$$thing{point_gable_status} = $gable_status;

}

sub
prune_points($$;$)
{
	my ($change_points, $points, $thing) = @_;
	my @deleted;
#	my $debug = 1;
	my $safe_loops;

	print "prune_points\n" if $debug;

	my $point_gable_status;
	if ($thing && $$thing{point_gable_status}) {
		# copy the reference so we can change the list contents
		$point_gable_status = $$thing{point_gable_status};
	}

	print "Start prune loop\n" if $debug;
	foreach my $cp0 (@$change_points) {
		print "Pruning from $cp0\n" if $debug;
		my @index;

		# adjust for points deleted already which will change offsets above them
		my $adjust = 0;
		foreach (@deleted) {
			$adjust++ if $_ <= $cp0;
		}
		$cp0 -= $adjust;

		# work out all four points in the end
		foreach my $i (0 .. 3) {
			push @index, ($cp0 + $i) % ($#$points+1);
		}

		my @delta_x;
		my @delta_y;
		foreach my $i (1 .. 3) {
			my ($curr_x, $curr_y) = @{$$points[$index[$i]]};
			my ($prev_x, $prev_y) = @{$$points[$index[$i-1]]};
			push @delta_x, $curr_x - $prev_x;
			push @delta_y, $curr_y - $prev_y;
			print "\tdx = $delta_x[$#delta_x], dy = $delta_y[$#delta_y]\n" if $debug;
		}

		if ($delta_x[0] + $delta_y[0] + $delta_x[2] + $delta_y[2] == 0) {
			# a regular end; just delete all four points
			foreach (sort { $b <=> $a } @index) {
				print "Deleting $_\n" if $debug;
				splice @$points, $_, 1;
				push @deleted, $_;

				# delete the matching entry in the point_gable_status list
				splice @$point_gable_status, $_, 1 if $point_gable_status;
			}
		}
		elsif ($delta_x[0] || $delta_y[0]) {
			# irregular end, ie like this:
			# 
			# --+
			#   +-+
			# ----+
			#
			# so we delete the middle 2 and move the 1st one onto the same line as the
			# 4th one.
			
			if ($delta_x[0]) {
				print "Irr X: " if $debug;
				if (abs($delta_x[0]) > abs ($delta_x[2])) {
					$$points[$index[3]][1] = $$points[$index[0]][1];
				}
				else {
					$$points[$index[0]][1] = $$points[$index[3]][1];
				}
			}
			else {
				print "Irr Y: " if $debug;
				if (abs($delta_y[0]) > abs ($delta_y[2])) {
					$$points[$index[3]][0] = $$points[$index[0]][0];
				}
				else {
					$$points[$index[0]][0] = $$points[$index[3]][0];
				}
			}
			foreach (sort { $b <=> $a } @index) {
				next if $_ == $index[0] || $_ == $index[3];
				print "Deleting $_\n" if $debug;
				splice @$points, $_, 1;
				push @deleted, $_;
				# delete the matching entry in the point_gable_status list
				splice @$point_gable_status, $_, 1 if $point_gable_status;
			}
		}
		else {
			print "?\n" if $debug;
		}

		last if $#$points == -1;
	}

	# don't bother doing this stuff if we've finished
	if ($#$points >= 0) {
		# Look for coincident points in the middle of a straight line
		print "Collinear coincident check\n" if $debug;

		# make a copy of the points list so we can change it
		my @points_copy = (@$points);
		# add the first 3 points to the end of the list so we can look forward 3 points
		# from each original point
		push @points_copy, @points_copy[0..2];
		# make a list of the directions between each point in the extended list
		my @dir;
		for (my $p = 0; $p < $#points_copy; $p++) {
			my $next_dir = get_direction($points_copy[$p], $points_copy[$p+1]);
			# mark coincident points 
			$next_dir = 4 unless defined($next_dir);
			push @dir, $next_dir;
			print "dir $p = $dir[$#dir]\n" if $debug;
		}

		# A* doesn't work here for some reason
		my $dir_str = pack "A" x ($#dir+1), @dir;
		print "CC dir_str = $dir_str\n" if $debug;

		my @bad_points;
		for (my $p = 0; $p <= $#$points; $p++) {
			if ($dir_str =~ /^([0-3])4\1/) {
				print "x4x sequence detected at $p\n" if $debug;
				push @bad_points, ($p + 1) % ($#$points+1), ($p + 2) % ($#$points+1);
			}
			# drop first char
			substr $dir_str, 0, 1, "";
		}

		# delete in reverse order so indexes remain ok while deleting
		foreach (reverse @bad_points) {
			print "Delete coincident collinear point $_\n" if $debug;
			splice @$points, $_, 1;
			splice @$point_gable_status, $_, 1 if $point_gable_status;
		}

		# check for mismatches in the gable list, ie we've deleted a start but not the matching end or vv
		my $prev = $$point_gable_status[$#$points];
		for (0 .. $#$point_gable_status) {
			# a point can be start and end but all ends still require the previous
			# point to be a start and vv
			if ($$point_gable_status[$_] & $GS_END && ! ($prev & $GS_START)) {
				$$point_gable_status[$_] &= ~($GS_END);
			}
			$prev = $$point_gable_status[$_];
		}
	}

}

sub 
find_tile_shapes($) {

	my $thing = shift;
	my @points = @{$$thing{base_points}};
#	my $debug = 1;

	print "find_tile_shapes\n" if $debug;

	my $prev_dir = get_direction($points[$#points], $points[0]);
	my %tile_shapes;

	# copy this for convenience
	my @point_gable_status;
	if ($$thing{point_gable_status}) {
		@point_gable_status = @{$$thing{point_gable_status}};
		foreach (@{$$thing{point_gable_status}}) {
			print "gs $_\n" if $debug;
		}
	}

	for (my $p = 0; $p <= $#points; $p++) {
		my $next = ($p + 1) % ($#points+1);
		printf "p %d = %d,%d, next %d = %d,%d\n", $p, @{$points[$p]}, $next, @{$points[$next]} if $debug;
		my $next_dir = get_direction($points[$p], $points[$next]);
		my ($x,$y) = @{$points[$p]};

		if (! defined($next_dir) && ! defined($prev_dir)) {
			# no dimensions at all; must be a single point
			return [ [ $x, $y, { nature => $ROOF, tile_shape => 6, shape => "$$thing{tile_color}_roof_LLLLLLLL" } ] ];
		}
		elsif (! defined($next_dir)) {
			$next_dir = ($prev_dir + 1) % 4;
		}
		elsif (! defined($prev_dir)) {
			$prev_dir = ($next_dir - 1) % 4;
		}

		# get the previous shape for this point; we may have two points on the
		# same xy location eg ridge ends; use a default shape if no prev exists.
		my $shape = $tile_shapes{"${x}_${y}"} || [ 'X','X','X','X','X','X','X','X' ];

		# set the low corner ends from from the incoming & outgoing direction
		my $in_corner = $prev_dir * 2;
		my $out_corner = ($next_dir * 2 + 2) % 8;

		# move in & out corner if we're a gable start &/or end
		if ($$thing{point_gable_status}) {
			$out_corner = ($out_corner - 2) % 8 if $point_gable_status[$p] & $GS_START;
			$in_corner = ($in_corner + 2) % 8 if $point_gable_status[$p] & $GS_END;
		}

		print "p = $p, x = $x, y = $y, prev dir = $prev_dir, next dir = $next_dir, low from $in_corner to $out_corner\n" if $debug;

		$$shape[$in_corner] = 'L';
		while ($in_corner++ != $out_corner) {
			$in_corner %= 8;
			$$shape[$in_corner] = 'L';
		}

		# save the start corner
		$tile_shapes{"${x}_${y}"} = $shape;

		# now do the run between this corner and the next (may be nothing)
		my ($next_x,$next_y) = @{$points[$next]};
		if (abs($next_x - $x) + abs($next_y - $y) > 1) {
			$in_corner = ($out_corner - 2) % 8;

			print "Side low from $in_corner to $out_corner\n" if $debug;

			while (1) {
				$x++ if $x < $next_x;
				$x-- if $x > $next_x;
				$y++ if $y < $next_y;
				$y-- if $y > $next_y;
				last if $x == $next_x && $y == $next_y;

				print " ($x,$y)" if $debug;

				# set the low points
				$shape = $tile_shapes{"${x}_${y}"} || [ 'X','X','X','X','X','X','X','X' ];

				if ($point_gable_status[$p] && $point_gable_status[$p] & $GS_START) {
					# set gable runs to SSSSSSSS
					$shape = $tile_shapes{"${x}_${y}"} || [ 'S','S','S','S','S','S','S','S' ];
				}
				else {
					# this creates a new version seeded from the previous scope's version
					my $in_corner = $in_corner;

					$$shape[$in_corner] = 'L';
					while ($in_corner++ != $out_corner) {
						$in_corner %= 8;
						$$shape[$in_corner] = 'L';
					}
				}

				# save the shape
				$tile_shapes{"${x}_${y}"} = $shape;
			}
			print "\n" if $debug;
		}

		$prev_dir = $next_dir;
	}

	my @resmap;

	foreach my $loc (keys %tile_shapes) {
		# add the first element to the end of the list so we can use
		# pattern matches to change the Xs to Ms; we don't need to add
		# the last element before the first because the first element
		# can't be an M.
		push @{$tile_shapes{$loc}}, ${$tile_shapes{$loc}}[0];
		# convert list to string
		$tile_shapes{$loc} = pack ("A" x 9, @{$tile_shapes{$loc}});
		# if we have a solid block (part of a gable end), skip all the roof stuff
		if ($tile_shapes{$loc} eq "SSSSSSSSS") {
			$tile_shapes{$loc} = "blue";
		}
		else {

			# any Xs next to Ls become Ms
			$tile_shapes{$loc} =~ s/XL/ML/g;
			$tile_shapes{$loc} =~ s/LX/LM/g;
			# any remaining Xs become Hs
			$tile_shapes{$loc} =~ s/X/H/g;

			# gable runs with mixtures of S & L; can happen when gable ends are
			# thin and opposite non-gables, ie on the base of an L shaped extension.
			if ($tile_shapes{$loc} =~ /S.*L|L.*S/) {
				$tile_shapes{$loc} =~ s/SL/ML/g;
				$tile_shapes{$loc} =~ s/LS/LM/g;
				$tile_shapes{$loc} =~ s/S/H/g;
			}

			# drop the last char (duplicate of first for pattern matching)
			substr $tile_shapes{$loc}, 8, 1, ""; 
			# print "$loc = $tile_shapes{$loc}\n" if $debug;

			# add the roof color
			$tile_shapes{$loc} = "$$thing{tile_color}_roof_" . $tile_shapes{$loc};
		}

		my ($x,$y) = $loc =~ /(\d+)_(\d+)/;

		# the tile_shape entry is ignored for non-roof tiles, eg the gable blocks
		push @resmap, [ $x, $y, { nature => $ROOF, tile_shape => 6, shape => $tile_shapes{$loc} } ];
	}

	return \@resmap;
}

sub 
pyramid_res_map {
	my $thing = shift;

	# check if we've calculated the map for this before
	if (defined ($$thing{cache_layer}) && $$thing{cache_layer} == $$thing{layer}) {
		return $$thing{cached_map};
	}

	# this attribute is derived from the nature of this function; other shapes
	# will find their heights differently.
	$$thing{final_height} = int ((min($$thing{x_dim},$$thing{y_dim})+1)/2)
		unless defined($$thing{final_height});

	my $curr_x = $$thing{x_dim} - 2 * $$thing{layer};
	my $curr_y = $$thing{y_dim} - 2 * $$thing{layer};

	if ($curr_x < 1 || $curr_y < 1) {
		print "Current layer gives <1 dim(s) for $$thing{id}\n";
		return;
	}

	# this routine will return a reference to this list
	my @resmap;

	# single-width maps are a special case
	if ($curr_x == 1 || $curr_y == 1) {
		if ($curr_x == 1) {
			if ($curr_y == 1) {
				push @resmap, [ 0, 0, { nature => $ROOF, tile_shape => 4 } ];
			}
			else {
				# vertical roof ridge

				# ends
				my $min_y = - int(($curr_y-1)/2);
				push @resmap, [ 0, $min_y, { angle => 0, nature => $ROOF, tile_shape => 5 } ];
				push @resmap, [ 0, $min_y + $curr_y - 1, { angle => 2, nature => $ROOF, tile_shape => 5 } ];

				# vert sides
				for (my $i = 0; $i < $curr_y - 2; $i++) {
					push @resmap, [ 0, $min_y + 1 + $i,
						{ angle => 0, nature => $ROOF, tile_shape => 2 } ];
				}
			}
		}
		else {
			# horizontal roof ridge

			# ends
			my $min_x = - int(($curr_x-1)/2);
			push @resmap, [ $min_x, 0, { angle => 3, nature => $ROOF, tile_shape => 5 } ];
			push @resmap, [ $min_x + $curr_x - 1, 0, { angle => 1, nature => $ROOF, tile_shape => 5 } ];

			# ridge
			for (my $i = 0; $i < $curr_x - 2; $i++) {
				push @resmap, [ $min_x + 1 + $i, 0,
					{ angle => 1, nature => $ROOF, tile_shape => 2 } ];
			}
		}
	}
	else {
		my $min_x = - int(($curr_x-1)/2);
		my $min_y = - int(($curr_y-1)/2);

		# corners
		push @resmap, [ $min_x, $min_y, { angle => 0, nature => $ROOF, tile_shape => 3 } ];
		push @resmap, [ $min_x + $curr_x - 1, $min_y, { angle => 1, nature => $ROOF, tile_shape => 3 } ];
		push @resmap, [ $min_x + $curr_x - 1, $min_y + $curr_y - 1, { angle => 2, nature => $ROOF, tile_shape => 3 } ];
		push @resmap, [ $min_x, $min_y + $curr_y - 1, { angle => 3, nature => $ROOF, tile_shape => 3 } ];

		# horiz sides
		for (my $i = 0; $i < $curr_x - 2; $i++) {
			push @resmap, [ $min_x + 1 + $i, $min_y,
				{ angle => 0, nature => $ROOF, tile_shape => 1 } ];
			push @resmap, [ $min_x + 1 + $i, $min_y + $curr_y - 1,
				{ angle => 2, nature => $ROOF, tile_shape => 1 } ];
		}

		# vert sides
		for (my $i = 0; $i < $curr_y - 2; $i++) {
			push @resmap, [ $min_x, $min_y + 1 + $i,
				{ angle => 3, nature => $ROOF, tile_shape => 1 } ];
			push @resmap, [ $min_x + $curr_x - 1, $min_y + 1 + $i,
				{ angle => 1, nature => $ROOF, tile_shape => 1 } ];
		}

	}
	if ($debug) {
		foreach my $res (@resmap) {
			my ($x, $y, $attribs) = @$res;
			print "$x,$y a $$attribs{angle}, t $$attribs{tile_shape}\n";
		}
	}

	# cache this map
	$$thing{cached_map} = \@resmap;
	$$thing{cache_layer} = $$thing{layer};

	return \@resmap;

}

sub 
single_peak_res_map
{
	my $thing = shift;
#	my $debug = 1;

	# check if we've calculated the map for this before
	if (defined ($$thing{cache_layer}) && $$thing{cache_layer} == $$thing{layer}) {
		return $$thing{cached_map};
	}

	if (! $$thing{base_points}) {
		die "No base points for single peak resmap";
	}

	# the final_height attribute is derived from the nature of this function; each shape
	# will find its height differently.
	if (! $$thing{final_height}) {
		# just run the loops with a copy of base_points and count
		# how many time we shrink. Could be calc'ed by analysing the points list
		# but would be v. diff.
		$$thing{final_height} = 1;
		# make a DEEP copy of the base points, since we're about to shrink, prune, etc
		my @points = map [ @$_ ], @{$$thing{base_points}};
		print "Calc'ing final height with $#points + 1 points\n" if $debug;
		while ($#points >= 0) {
			my $change_points = find_next_change(\@points);
			my $safe_loops = shift @$change_points;
			print "Safe_loops recalc'ed, now $safe_loops\n" if $debug;
			while ($safe_loops--) {
				resize_points(-1, \@points);
				$$thing{final_height}++;
				print "Final height now $$thing{final_height}\n" if $debug;
			}
			prune_points($change_points, \@points);
		}
		print "Single peak height = $$thing{final_height}\n" if $debug;
	}

	if ($$thing{layer} > 0) {
		# not the first layer, so we've finished a level and have to do the next one.
		# if $safe_loops is >0, we can just shrink the points, otherwise we have
		# to prune first and then shrink.

		# make sure we have safe_loops > 0
		do {
			if (defined($$thing{safe_loops}) && $$thing{safe_loops} == 0) {
				print "Safe_loops == 0, pruning\n" if $debug;
				# we've previously called find_next_change to find safe_loops, and
				# we've subsequently had that many levels done. Prune and then find_next_change
				# again.
				prune_points($$thing{change_points}, $$thing{base_points});
				# check that pruning hasn't removed all our points; if final_height
				# was calc'ed correctly, this shouldn't happen (we'll only get 
				# called the correct amount of times).
				if ($#{$$thing{base_points}} < 0) {
					print "No more points in single_peak\n" if $debug;
					return [];
				}

			}
			if (! $$thing{safe_loops}) {
				# Either safe_loops is 0 (and we just pruned) or we've never called 
				# find_next_change; either way, call it now.
				$$thing{change_points} = find_next_change($$thing{base_points});
				$$thing{safe_loops} = shift @{$$thing{change_points}};
				print "Safe_loops recalc'ed, now $$thing{safe_loops}\n" if $debug;
			}
		}
		while $$thing{safe_loops} == 0;

		# keep track of how many time's we've shrunk since pruning; we're assuming
		# safe_loops will be >0 after
		$$thing{safe_loops}--;
		print "Shrinking, safe_loops now $$thing{safe_loops}\n" if $debug;
		resize_points(-1,$$thing{base_points});
	}

	# this routine will return this list reference
	my $resmap = find_tile_shapes($thing);

	if ($debug) {
		foreach my $res (@$resmap) {
			my ($x, $y, $attribs) = @$res;
			print "$x,$y shape $$attribs{shape}\n";
		}
	}

	# cache this map
	$$thing{cached_map} = $resmap;
	$$thing{cache_layer} = $$thing{layer};

	return $resmap;

}

sub 
single_peak_gable_res_map
{
	my $thing = shift;
#	my $debug = 1;

	# check if we've calculated the map for this before
	if (defined ($$thing{cache_layer}) && $$thing{cache_layer} == $$thing{layer}) {
		return $$thing{cached_map};
	}

	print "single_peak_gable_res_map, layer $$thing{layer}\n" if $debug;

	if (! $$thing{base_points}) {
		die "No base points for single peak gable resmap";
	}

	if ($$thing{layer} == 0) {
		# first layer; do initial tasks

		# find the gable status list for the initial points; we'll update this
		# when we prune or when we resize but only to keep it in sync, we don't
		# add any more points (except if we split a start+end point into 2)
		find_gable_statuses($thing);
	}

	if ($$thing{layer} > 0) {
		# not the first layer, so we've finished a level and have to do the next one.
		# if $safe_loops is >0, we can just shrink the points, otherwise we have
		# to prune first and then shrink.

		# make sure we have safe_loops > 0
		do {
			if (defined($$thing{safe_loops}) && $$thing{safe_loops} == 0) {
				print "Safe_loops == 0, pruning\n" if $debug;
				# we've previously called find_next_change to find safe_loops, and
				# we've subsequently had that many levels done. Prune and then find_next_change
				# again.
				prune_points($$thing{change_points}, $$thing{base_points}, $thing);
				# check that pruning hasn't removed all our points; if final_height
				# was calc'ed correctly, this shouldn't happen (we'll only get 
				# called the correct amount of times).
				if ($#{$$thing{base_points}} < 0) {
					print "No more points in single_peak_gable\n" if $debug;
					return undef;
				}

			}
			unless ($$thing{safe_loops}) {
				# Either safe_loops is 0 (and we just pruned) or we've never called 
				# find_next_change; either way, call it now.
				$$thing{change_points} = find_next_change($$thing{base_points}, $thing);
				$$thing{safe_loops} = shift @{$$thing{change_points}};
				print "Safe_loops recalc'ed, now $$thing{safe_loops}\n" if $debug;
				die "safe_loops undefined" unless defined($$thing{safe_loops});
			}
		}
		while $$thing{safe_loops} == 0;

		# keep track of how many time's we've shrunk since pruning; we know
		# safe_loops will be >0 after the previous loop
		$$thing{safe_loops}--;
		print "Shrinking, safe_loops now $$thing{safe_loops}\n" if $debug;
		resize_points(-1,$$thing{base_points}, $thing);
	}

	# this routine will return this list reference
	my $resmap = find_tile_shapes($thing);

	if ($debug) {
		foreach my $res (@$resmap) {
			my ($x, $y, $attribs) = @$res;
			print "$x,$y shape $$attribs{shape}\n";
		}
	}

	# cache this map
	$$thing{cached_map} = $resmap;
	$$thing{cache_layer} = $$thing{layer};

	return $resmap;

}

sub
make_plan()
{
	my $nbr_changed_corners = ceil(rand(4));
	# print "hack; ncc = $nbr_changed_corners\n";

	my @new_corner_move = ( [1,-1], [1,1], [-1,1], [-1,-1],);

	my @corner_move = ( [1,0], [0,1], [-1,0], [0,-1],);
	my $x_dir = ${$corner_move[3]}[0];
	my $y_dir = ${$corner_move[3]}[1];

	# note that axes are screen, not cartesian, ie origin is top left.
	# initial points, a simple square
	my @corner = ( { x => 0, y => 0 }, { x => 1, y => 0 }, { x => 1, y => 1 }, { x => 0, y => 1 }, );
	# list of all points
	my @new_corners;
	my $x = ${$corner[3]}{x};
	my $y = ${$corner[3]}{y};

	foreach (0..3) {
		# print "Current location = $x,$y, dir = $x_dir,$y_dir\n";

		# place this corner, ie move it into the line of direction 
		# at least 1 along that line from the current corner
		if ($x_dir) {
			if ($_ == 3 && $nbr_changed_corners > 0) {
				# boy, this sucks; for the last corner, if it is followed by
				# an extra corner (thus making a cross), we have to manually hack
				# the new pos so it lines up with the first corner...
				${$corner[$_]}{x}++;
			}
			${$corner[$_]}{x} = $x_dir > 0 ? max ($x+1, ${$corner[$_]}{x}) : min ($x-1, ${$corner[$_]}{x}); 
			${$corner[$_]}{y} = $y;
		}
		else {
			${$corner[$_]}{x} = $x;
			${$corner[$_]}{y} = $y_dir > 0 ? max ($y, ${$corner[$_]}{y}) : min ($y-1, ${$corner[$_]}{y}); 
		}
		# current position to new corner
		$x = ${$corner[$_]}{x};
		$y = ${$corner[$_]}{y};
		# print "Place corner $_ at $x,$y\n";
		push @new_corners, [ $x,$y ];
		# switch direction for corner
		$x_dir = ${$corner_move[$_]}[0];
		$y_dir = ${$corner_move[$_]}[1];
		# maybe draw corner
		if ($nbr_changed_corners-- > 0) {
			my $dx = ${$new_corner_move[$_]}[0];
			my $dy = ${$new_corner_move[$_]}[1];
			# move the current position
			# draw the lines; we draw the line across the current direction first
			if ($x_dir) {
				$x += $x_dir;
				push @new_corners, [ $x,$y ];
				$y += $dy;
				push @new_corners, [ $x,$y ];
			}
			else {
				$y += $y_dir;
				push @new_corners, [ $x,$y ];
				$x += $dx;
				push @new_corners, [ $x,$y ];
			}
		}
	}

	# convert the list of points to a list of positive unit (ie based on 1x1) offsets
	# We must do this in several stages (offset, protrusions, minimums, adjusted offsets)
	# since finding protrusions is much easier using offsets,

	my @offset;

	# simple offsets
	my $prev_x = 0;
	my $prev_y = 0;
	foreach my $point (@new_corners) {
		my ($x,$y) = @$point;
		push @offset, [ $x - $prev_x, $y - $prev_y ];
		$prev_x = $x;
		$prev_y = $y;
	}

	# replace the 0,0 offset from the start of the list with a pair
	# representing the offset from the final point back to the origin
	# so we can look "around" the end of the list to the neighbouring offset.
	shift @offset;
	unshift @offset, [ $prev_x ? -$prev_x : 0, $prev_y ? -$prev_y : 0 ];

	# find protrusions ; list is indexes of the middle offset
	my @protrusions;
	for (my $i=0;$i <= $#offset; $i++) {
		my ($x,$y) = @{$offset[$i]};
		($prev_x, $prev_y) = @{$offset[$i > 0 ? $i-1 : $#offset ]};
		my ($next_x, $next_y) = @{$offset[ $i < $#offset ? $i+1 : 0]};
		if ((abs($x) == 1 && $prev_x == 0 && $next_x == 0 && ($prev_y * $next_y < 0))
			|| (abs($y) == 1 && $prev_y == 0 && $next_y == 0 && ($prev_x * $next_x < 0)))
		{
			push @protrusions, $i;
		}
	}
	# add a dummy meaning "no protrusion"
	push @protrusions, -1;

	# pick one index at random
	# looks bad, but we're just getting and assigning a random index and then
	# testing the element at that index.
	if ((my $pro_index = $protrusions[ int(rand()*($#protrusions + 1))]) > -1) {

		# stretch the offsets (ie increase their magnitude) to either side
		# of the protruding offset
		my $next_index = $pro_index < $#offset ? $pro_index + 1 : 0;
		my $prev_index = $pro_index > 0 ? $pro_index - 1 : $#offset;
		if (${$offset[$pro_index]}[0]) {
			${$offset[$next_index]}[1] += ${$offset[$next_index]}[1] > 0 ? 1 : -1;
			${$offset[$prev_index]}[1] += ${$offset[$prev_index]}[1] > 0 ? 1 : -1;
		}
		else {
			${$offset[$next_index]}[0] += ${$offset[$next_index]}[0] > 0 ? 1 : -1; 
			${$offset[$prev_index]}[0] += ${$offset[$prev_index]}[0] > 0 ? 1 : -1;
		}
	}

	# restore the 0,0 offset since we want this when actually using the offsets.
	shift @offset;
	unshift @offset, [ 0,0 ];

	my $min_x = 0;
	my $min_y = 0;
	my $max_x = 0;
	my $max_y = 0;
	my $real_x = 0;
	my $real_y = 0;
	# find the minimums so the real position never goes "below" the origin; this means we can specify a 
	# location point at the top left of the area.
	foreach my $offset_info (@offset) {
		my ($x,$y) = @$offset_info;
		$real_x += $x;
		$real_y += $y;
		$min_x = $real_x if $real_x < $min_x;
		$min_y = $real_y if $real_y < $min_y;
		$max_x = $real_x if $real_x > $max_x;
		$max_y = $real_y if $real_y > $max_y;
	}
	shift @offset;
	# avoid unsightly -0
	unshift @offset, [ $min_x ? -$min_x : 0, $min_y ? -$min_y : 0 ];

	return \@offset, $max_x - $min_x, $max_y - $min_y;

}

sub
fit_plan($$$$$)
{
	my ($point, $width, $height, $min_grid_size, $rect) = @_;
	my $reverse = 0;
	my $debug = 1;

	# create a local copy of the map so we can reverse it without affecting
	# the real one
	my @new_point;
	foreach (@$point) {
		push @new_point, [ @$_ ];
	}

	if ($#$rect != 3) {
		print "fit_plan: rect (@$rect) does not have 4 entries\n";
		return;
	}

	print "fit_plan: $width $height $min_grid_size, @$rect\n" if $debug;
	map { print "\t@$_\n"; } @new_point if $debug;

	my $rect_width = $$rect[2] - $$rect[0];
	my $rect_height = $$rect[3] - $$rect[1];

	# we need to swap the point x&y coords if the plan and the rect 
	# run in different directions, eg long sides aren't both x or y.
	# Do nothing if either area is a square.
	if ($width > $height && $rect_width < $rect_height) {
		# the last side in the building is a virtual one, made by going
		# from the last explicit corner back to the origin. We have to know
		# the offsets for this move since this side will not be virtual in
		# the reversed map, so run through the points and find the offset
		# from where we end up to the origin.

		print "Reversing to fit\n" if $debug;
		# take the origin points off the list
		my ($orig_x, $orig_y) = @{shift @new_point};
		# take the first offset off the list; this offset will be the virtual one 
		# in the reversed list
		my ($x,$y) = @{shift @new_point};
		my ($curr_x, $curr_y) = ($orig_x + $x, $orig_y + $y);
		# run through the rest of the list updating the location
		foreach (@new_point) {
			my ($x,$y) = @$_;
			$curr_x += $x;
			$curr_y += $y;
		}
		# add the offset from the final location back to the origin
		push @new_point, [ $orig_x - $curr_x, $orig_y - $curr_y ];
		# reverse the list
		@new_point = reverse @new_point;
		# change the signs and swap x & y coords
		foreach (@new_point) {
			my ($x,$y) = @$_;
			$$_[0] = $y * -1;
			$$_[1] = $x * -1;
		}
		# add the x-y swapped (but not sign changed) origin at the head of the list
		unshift @new_point, [ $orig_y, $orig_x ];
		# swap plan dimensions
		my $tmp = $width;
		$width = $height;
		$height = $tmp;
		if ($debug) {
			print "After reverse:\n";
			map { print "\t@$_\n"; } @new_point;
		}
	}

	# calculate the dimension of the unit square in the rect.
	# PAD is the free area around the building
	my $PAD = $min_grid_size > 4 ? 6 : 4;

	my $x_grid = int(($rect_width - $PAD*2) / $width);
	my $y_grid = int(($rect_height - $PAD*2) / $height);
	print "Calculated x,y grids = $x_grid, $y_grid\n" if $debug;

	# we want to find values of x_grid and y_grid such that the grids
	# have a common factor, and we will use the pair
	# of values with the greatest sum.
	my ($best_x, $best_y) = (0,0);
	foreach my $test_x ($min_grid_size .. $x_grid ) {
		foreach my $test_y ($min_grid_size .. $y_grid ) {
			# we don't care about what order we test these factors in,
			# the code in fit_plan will do that
			print "Looking for factors, x = $test_x, y = $test_y\n" if $debug;
			foreach my $grid_factor (1 .. 4) {
				print "gf = $grid_factor\n" if $debug;
				# skip unless exact factor
				if ($test_x % $grid_factor) {
					print "gf not exact factor of $test_x\n" if $debug;
					next;
				}
				my $column_grid = $test_x / $grid_factor;
				# skip if we're too small
				if ($column_grid < $column_wall_min{$column_size{$min_grid_size}}) {
					print "cg $column_grid too small\n" if $debug;
					next;
				}
				# skip unless the column spacing works for the y grid as well
				if ($test_y % $column_grid) {
					print "cg $column_grid not exact factor of $test_y\n" if $debug;
					next;
				}
				print "valid column_grid = $column_grid\n" if $debug;
				if (($test_x + $test_y) > ($best_x + $best_y)) {
					print "New best $test_x, $test_y\n" if $debug;
					($best_x, $best_y) = ($test_x, $test_y);
				}
			}
		}
	}
	($x_grid, $y_grid) = ($best_x, $best_y);

	# make sure we have a minimum grid size
	if (min($x_grid,$y_grid) < $min_grid_size) {
		print "Smaller of $x_grid, $y_grid < $min_grid_size\n" if $debug;
		return 0 ;
	}

	# make sure the ratio between x & y grids is no more than 3
	# this overrides the common-factor work but we know we'll
	# get a good factor for column spacing, eg 3.
	$x_grid = min($x_grid, $y_grid*3) if $x_grid > $y_grid;
	$y_grid = min($y_grid, $x_grid*3) if $x_grid < $y_grid;

	# change the building rect to be the space we need, not the original space
	$$rect[2] = $$rect[0] + $x_grid * $width + $PAD * 2;
	$$rect[3] = $$rect[1] + $y_grid * $height + $PAD * 2;

	# convert the point offsets to real grid coords
	my $prev_x = $$rect[0] + $PAD;
	my $prev_y = $$rect[1] + $PAD;
	foreach (@new_point) {
		my ($x,$y) = @$_;
		$prev_x = $$_[0] = $prev_x + $x * $x_grid;
		$prev_y = $$_[1] = $prev_y + $y * $y_grid;
	}

	# change the contents of the argument listref to the new list
	@$point = ($x_grid, $y_grid, @new_point);
	print "Plan fits ok with $x_grid, $y_grid\n" if $debug;
	return 1;

}

sub
tracker {
	my ($canvas, $x, $y) = @_;
	$x = $canvas->canvasx($x);
	$y = $canvas->canvasx($y);

	my $origin_x = 10;
	my $origin_y = 10;

	# move the origin according to the spin
	if ($spin == 0) {
		$origin_y += $GX * $image_y_offset;
	}
	elsif ($spin == 1) {
		$origin_x += $GY * $image_x_offset;
	}
	elsif ($spin == 2) {
		$origin_x += ($GX+$GY) * $image_x_offset;
		$origin_y += $GY * $image_y_offset;
	}
	elsif ($spin == 3) {
		$origin_x += $GX * $image_x_offset;
		$origin_y += ($GX+$GY) * $image_y_offset;
	}

	# move the y offset down to allow for building height
	$origin_y += 15 * $image_z_offset;

	# elements in spin matrix are:
	# x-coord x factor, x-coord y factor, y-coord x factor, y-coord y factor
	my $spin_matrix = (
		[ 1,1,-1,1 ],
		[ 1,-1,1,1 ],
		[ -1,-1,1,-1 ],
		[ -1,1,-1,-1 ]
		)[$spin];

	# hack
	#$y -= 2;

	print "x,y = $x,$y, origin = $origin_x, $origin_y\n" if $debug;

	my $x_grid = int (( $$spin_matrix[3] * ($x - $origin_x) + 2 * $$spin_matrix[1] * ($origin_y - $y ) ) /
		($image_x_offset * ($$spin_matrix[0] * $$spin_matrix[3] - $$spin_matrix[1] * $$spin_matrix[2])));
	my $y_grid = int(( 2 * $$spin_matrix[0] * ($y - $origin_y) + $$spin_matrix[2] * ($origin_x - $x ) ) /
		($image_y_offset * ($$spin_matrix[0] * $$spin_matrix[3] - $$spin_matrix[1] * $$spin_matrix[2])));

	# the above produces y grid 2x the correct value...don't remember how it works so just fix it now.
	$y_grid >>= 1;

	# find the cell at this point
	my $found_cell = undef;
	foreach my $cell (@{$tree{$CELL}}) {
		print " ($$cell{x},$$cell{y})" if $debug > 1;
		$found_cell = $cell and last if $$cell{x} == $x_grid && $$cell{y} == $y_grid;
	}
	print "\n" if $debug > 1;

	if ($found_cell) {
		if ($$found_cell{object}) {
			inspect(${$$found_cell{object}}{id});
		}
		else {
			print "Cell at $x_grid, $y_grid has no object\n" if $debug;
		}
	}
	else {
		print "Nothing at $x_grid, $y_grid\n" if $debug;
	}

=for comment
	print "x:   ";
	foreach $x (16..40) {
		print "  $x  ";
	}
	print "\n";
	foreach $y (292 .. 310) {
		print "$y: ";
		foreach $x (16..40) {

			my $x_grid = int (( $$spin_matrix[3] * ($x - $origin_x) + 2 * $$spin_matrix[1] * ($origin_y - $y ) ) /
				(6 * ($$spin_matrix[0] * $$spin_matrix[3] - $$spin_matrix[1] * $$spin_matrix[2])));
			my $y_grid = int(( 2 * $$spin_matrix[0] * ($y - $origin_y) + $$spin_matrix[2] * ($origin_x - $x ) ) /
				(6 * ($$spin_matrix[0] * $$spin_matrix[3] - $$spin_matrix[1] * $$spin_matrix[2])));

			#print "Tracker: x = $x, y = $y, x_grid = $x_grid, y_grid = $y_grid\n";
			# print " (",abs($x_grid),",",abs($y_grid),")";
			printf " %+1d,%+1d", $x_grid, $y_grid;
		}
		print "\n";
	}
=cut

}

sub 
render_tk_3d(;$) 
{

	my $full_refresh = shift;

	my $origin_x = 10;
	my $origin_y = 10;

	$full_refresh |= $gen % 10 == 0;

	# clear canvas
	$td_canvas->delete("all") if $full_refresh;

	my $seek_color_size = int($lifespan{$CELL} / 6) + 1;

	# create a hash of hashes, keyed by x & y coords. Use a hash to
	# make scanning the sparse result quicker.
	my $z_hash = {};
	my $y_hash;
	my $x_hash;

	# the generic roof style needs to know how to "spin" the tile shapes;
	# the shapes are 8-char strings and we move 2 from end to start for
	# each spin level, so this factor shows many remain from the front end.
	my $spin_factor = 8 - $spin * 2;

	# add cells to hash
	foreach my $cell (@{$tree{$CELL}}) {
		my $color;
		if ($$cell{state} & $SEEKING_GROUP) {
			$color = int($$cell{life} / $seek_color_size);
			$color = $seek_color{$color};
		}
		else {
			next unless $full_refresh;
			if ($$cell{nature} == $ROOF) {
				if ($$cell{tile_shape} == 4) {
					# point
					$color = "blue_roof_point";
				}
				elsif ($$cell{tile_shape} == 3) {
					# corner
					$color = "blue_roof_" . qw(nw ne se sw)[($spin + $$cell{angle}) % 4];
				}
				elsif ($$cell{tile_shape} == 2) {
					# ridge
					$color = "blue_ridge_" . ($spin % 2 == $$cell{angle} ? 'ns' : 'ew');
				}
				elsif ($$cell{tile_shape} == 1) {
					# normal slant tile
					$color = "blue_roof_" . qw(n e s w)[($spin + $$cell{angle}) % 4];
				}
				elsif ($$cell{tile_shape} == 5) {
					# ridge end
					$color = "blue_ridge_" . qw(n e s w)[($spin + $$cell{angle}) % 4];
				}
				elsif ($$cell{tile_shape} == 6) {
					# new roof general style; just store the spin-adjusted shape in the
					# cell hash and cope with it splitting into 2 images when actually
					# rendering.
					($color = $$cell{shape}) =~ s/(.+_roof_)(.{$spin_factor})(.*)/$1$3$2/;
				}
				else {
					print "Roof $$cell{id} has unknown tile_shape\n";
				}
			}
			else {
				$color = $state_color{$$cell{state}};
			}
		}

		$$z_hash{$$cell{z}} = {} unless $$z_hash{$$cell{z}};
		$y_hash = $$z_hash{$$cell{z}};

		$$y_hash{$$cell{y}} = {} unless $$y_hash{$$cell{y}};
		$x_hash = $$y_hash{$$cell{y}};

		$$x_hash{$$cell{x}} = $color;
	}
	# add the origin
	${${$$z_hash{0}}{0}}{0} = 'blue';

	if (0) {
		# draw a grid
		my $x_across = ($GX+1) * $image_x_offset;
		my $y_across = ($GY+1) * $image_x_offset;
		my $x_down = ($GX+1) * $image_y_offset;
		my $y_down = ($GY+1) * $image_y_offset;
		my $grid_down = 7;
		my $origin_y = 10 + $GX * $image_y_offset + 15 * $image_z_offset;

		$td_canvas->createLine($origin_x, $origin_y + $grid_down, $origin_x + $x_across, $origin_y - $x_down + $grid_down);
		$td_canvas->createLine($origin_x, $origin_y + $grid_down, $origin_x + $y_across, $origin_y + $y_down + $grid_down);
		$td_canvas->createLine($origin_x + $x_across, $origin_y - $x_down + $grid_down, 
			$origin_x + $x_across + $y_across, $origin_y - $x_down + $y_down + $grid_down); 
		$td_canvas->createLine($origin_x + $y_across, $origin_y + $y_down + $grid_down,
			$origin_x + $y_across + $x_across, $origin_y + $y_down - $x_down + $grid_down);
	}

	# move the origin according to the spin
	if ($spin == 0) {
		$origin_y += $GX * $image_y_offset;
	}
	elsif ($spin == 1) {
		$origin_x += $GY * $image_x_offset;
	}
	elsif ($spin == 2) {
		$origin_x += ($GX+$GY) * $image_x_offset;
		$origin_y += $GY * $image_y_offset;
	}
	elsif ($spin == 3) {
		$origin_x += $GX * $image_x_offset;
		$origin_y += ($GX+$GY) * $image_y_offset;
	}
	# move the y offset down to allow for building height
	$origin_y += 15 * $image_z_offset;
	print "Spin = $spin, origin = $origin_x, $origin_y\n" if $debug;

	# move through the coordinates in an appropriate direction for the spin
	my (@x_list, @y_list);

	# elements in spin matrix are:
	# x-coord x factor, x-coord y factor, y-coord x factor, y-coord y factor
	my $spin_matrix = (
		[ 1,1,-1,1 ],
		[ 1,-1,1,1 ],
		[ -1,-1,1,-1 ],
		[ -1,1,-1,-1 ]
		)[$spin];

	# display the hashes
	foreach my $z (sort numeric keys %$z_hash) {
		$y_hash = $$z_hash{$z};
		@y_list = $spin < 2 ? sort numeric keys %$y_hash : sort rev_numeric keys %$y_hash;
		foreach my $y (@y_list) {
			$x_hash = $$y_hash{$y};
			@x_list = ($spin == 1 || $spin == 2) ? sort numeric keys %$x_hash : sort rev_numeric keys %$x_hash;
			foreach my $x (@x_list) {
				# print "x = $x, y = $y, color = $$x_hash{$x}\n";
				my $x_coord =
					$origin_x + $x * $image_x_offset * $$spin_matrix[0] + $y * $image_x_offset * $$spin_matrix[1];
				my $y_coord =
					$origin_y + $x * $image_y_offset * $$spin_matrix[2] + $y * $image_y_offset * $$spin_matrix[3] - $z * $image_z_offset;

				# we might have a generic roof shape, for which we need to display 2 images
				if ($$x_hash{$x} =~ /(.+_roof_)(([HL])...)((.)...)/o) {
					# yep, roof.
					# following the color chunk, we have an 8 char string holding the spin-corrected shape of the roof
					# tile, eg LLLMHHHM (west slant, spin 0). The first 5 chars give us the
					# left side, the last 4 chars plus the first one give us the right side.

					# we got out the parts we need in the test; make the 2 tile names.
					$td_canvas->createImage( $x_coord, $y_coord, -image => $td_img{"${1}0$2$5"}, -anchor => 'nw');
					$td_canvas->createImage( $x_coord, $y_coord, -image => $td_img{"${1}1$4$3"}, -anchor => 'nw');

				}
				else {
					die "No image for $$x_hash{$x}" unless $td_img{$$x_hash{$x}};
					$td_canvas->createImage(
						$x_coord, $y_coord,
						-image => $td_img{$$x_hash{$x}},
						-anchor => 'nw');
				}
			}
		}
	}

=for comment

	# corners
	$td_canvas->createImage( $origin_x, $origin_y, -image => $td_img{blue}, -anchor => 'nw');
	$td_canvas->createImage( $origin_x + $GX * $image_x_offset, $origin_y - $GX * $image_y_offset, -image => $td_img{blue}, -anchor => 'nw');
	$td_canvas->createImage( $origin_x + $GY * $image_x_offset, $origin_y + $GY * $image_y_offset, -image => $td_img{blue}, -anchor => 'nw');
	$td_canvas->createImage( $origin_x + $GX * $image_x_offset + $GY * $image_x_offset, $origin_y - $GX * $image_y_offset + $GY * $image_y_offset, -image => $td_img{blue}, -anchor => 'nw');

=cut

	$td_canvas->idletasks;

}

sub 
render_tk() 
{

	my $seek_color_size = int($lifespan{$CELL} / 6) + 1;
	my $canvas = $td_canvas;

	# clear canvas
	$canvas->delete("all");

	my $image_width = $small_img{red}->width;
	my $image_height = $small_img{red}->height;

	# add cells to map
	foreach my $cell (@{$tree{$CELL}}) {
		my $color;
		if ($$cell{state} & $SEEKING_GROUP) {
			$color = int($$cell{life} / $seek_color_size);
			$color = $seek_color{$color};
		}
		else {
			$color = $state_color{$$cell{state}};
		}
		$canvas->createImage(($$cell{y}+1)*$image_width,($GX-$$cell{x})*$image_height,-image => $small_img{$color});
	}

	# corners
	$canvas->createImage($image_width,$GX*$image_width,-image => $small_img{blue});
	# $canvas->createImage($GX*$image_width,$image_width,-image => $small_img{blue});
	# $canvas->createImage($image_width,$GY*$image_height,-image => $small_img{blue});
	# $canvas->createImage($GX*$image_width,$GY*$image_height,-image => $small_img{blue});

	$canvas->idletasks;

}

sub
get_distance($$) 
{
	my (@x, @y);

	foreach my $thing (@_) {
		if ($$thing{type} == $CELL) {
			push @x, $$thing{x};
			push @y, $$thing{y};
		}
		elsif ($$thing{type} == $WALL) {
			# measure from midpoint
			if ($$thing{horiz}) {
				push @x, $$thing{end_1} + $$thing{len} / 2;
				push @y, $$thing{line};
			}
			else {
				push @x, $$thing{line};
				push @y, $$thing{end_1} + $$thing{len} / 2;
			}
		}
		elsif ($$thing{type} == $RES) {
			push @x, $$thing{x};
			push @y, $$thing{y};
		}
		elsif ($$thing{type} == $ROOM) {
			my $rect = $$thing{rect};
			push @x, $$rect[0] + ($$rect[2] - $$rect[0])/2;
			push @y, $$rect[1] + ($$rect[3] - $$rect[1])/2;
		}
		else {
			print "Unknown type of thing ($$thing{type}) in get_distance\n";
			return undef;
		}
	}

	return abs(sqrt(($x[0] - $x[1])**2 + ($y[0] - $y[1])**2));
}

sub
rectangles_intersect($$) 
{
	my ($rect1, $rect2) = @_;

	# rectangles are described by x1,y1,x2,y2, top left to bottom right.
	# indexes
	my @rect1 = @$rect1;
	my @rect2 = @$rect2;

	# it's easier to check for non-intersection and negate it; for
	# that, at least one set of coords (x or y) must fail to intersect,
	# ie the range for rect1 lies wholly above or below the corres range
	# for rect2. Since we have ordered corners, relative positions are
	# fairly easy to do, eg if left1 > right2, we know 1 is above 2.

	return ! ($rect1[0] > $rect2[2] || $rect2[0] > $rect1[2] 
		|| $rect1[1] > $rect2[3] || $rect2[1] > $rect1[3]);

}

sub
update_resonances($) 
{

	my $thing = shift;
	my (@resonances, @valid_resonances);
	my %type_pri = (
		$CELL => 1,
		$WALL => 2,
		$MAP_WALL => 2,
		$ROOF => 3,
		$PEDIMENT => 4,
		$COLUMN => 5,
		$RESKEY_THING => 5,
		);
	my $debug = 0;

	print "update_resonances for $$thing{id}\n" if $debug;

	if ($$thing{type} == $CELL) {
		push @resonances, { x => $$thing{x}+1, y => $$thing{y} } if $$thing{x} < $GX-1;
		push @resonances, { x => $$thing{x}-1, y => $$thing{y} } if $$thing{x} > 0;
		push @resonances, { x => $$thing{x}, y => $$thing{y}+1 } if $$thing{y} < $GY-1;
		push @resonances, { x => $$thing{x}, y => $$thing{y}-1 } if $$thing{y} > 0;
	}
	elsif ($$thing{type} & ($WALL | $PEDIMENT)) {
		if ($$thing{horiz}) {
			my $end_1_limit = defined($$thing{final_end_1}) ? $$thing{final_end_1} : 0;
			my $end_2_limit = defined($$thing{final_end_2}) ? $$thing{final_end_2} : $GX-1;
			push @resonances,
				{ x => $$thing{end_1}-1, y => $$thing{line} } if $$thing{end_1} > $end_1_limit;
			push @resonances,
				{ x => $$thing{end_2}+1, y => $$thing{line} } if $$thing{end_2} < $end_2_limit
					&& (!defined($$thing{final_end_1})
						|| $$thing{final_end_1} != $$thing{final_end_2});
		}
		else {
			my $end_1_limit = defined($$thing{final_end_1}) ? $$thing{final_end_1} : 0;
			my $end_2_limit = defined($$thing{final_end_2}) ? $$thing{final_end_2} : $GY-1;
			push @resonances,
				{ x => $$thing{line}, y => $$thing{end_1}-1 } if $$thing{end_1} > $end_1_limit;
			push @resonances,
				{ x => $$thing{line}, y => $$thing{end_2}+1 } if $$thing{end_2} < $end_2_limit
					&& (!defined($$thing{final_end_1})
						|| $$thing{final_end_1} != $$thing{final_end_2});
		}
	}
	elsif ($$thing{type} == $ROOF) {
		my $line = $$thing{line};
		$line += $$thing{height} * (($$thing{angle} % 3) ? -1 : 1) if $$thing{tile_shape} == 1;
		if ($$thing{horiz}) {
			my $end_1_limit = defined($$thing{final_end_1}) ? $$thing{final_end_1} : 0;
			my $end_2_limit = defined($$thing{final_end_2}) ? $$thing{final_end_2} : $GX-1;
			push @resonances,
				{ x => $$thing{end_1}-1, y => $line } if $$thing{end_1} > $end_1_limit;
			push @resonances,
				{ x => $$thing{end_2}+1, y => $line } if $$thing{end_2} < $end_2_limit;
		}
		else {
			my $end_1_limit = defined($$thing{final_end_1}) ? $$thing{final_end_1} : 0;
			my $end_2_limit = defined($$thing{final_end_2}) ? $$thing{final_end_2} : $GY-1;
			push @resonances,
				{ x => $line, y => $$thing{end_1}-1 } if $$thing{end_1} > $end_1_limit;
			push @resonances,
				{ x => $line, y => $$thing{end_2}+1 } if $$thing{end_2} < $end_2_limit;
		}
	}
	elsif ($$thing{type} & $MAP_GROUP) {
		my $base_x = $$thing{x};
		my $base_y = $$thing{y};

=for comment
		my @heights = @{$$thing{heights}};
		foreach my $res (@{$$thing{resmap}}) {
			my $height = shift @heights;
			next if $height == $$thing{final_height};
			my ($x,$y) = @$res;
			push @resonances, { x => $base_x + $x, y => $base_y + $y };
		}
=cut

		my $resmap = $$thing{resmap};
		my $heights = $$thing{heights};
		for (my $i=0; $i <= $#$resmap; $i++) {
			next if $$heights[$i] == $$thing{final_height};
			my ($x,$y) = @{$$resmap[$i]};
			push @resonances, { x => $base_x + $x, y => $base_y + $y, res_index => $i };
		}
	}
	elsif ($$thing{type} & $RESKEY_GROUP) {
		my $base_x = $$thing{x};
		my $base_y = $$thing{y};
		my $layer = $$thing{layer};
		my $filled_res = $$thing{filled_res};
		my $resmap = $$thing{resfunc}
			?  &{$$thing{resfunc}}($thing)
			: ${$$thing{reskey}}{$layer};
		if ($resmap) {
			for (my $i=0; $i <= $#$resmap; $i++) {
				next if $$filled_res[$i];
				my ($x,$y,undef) = @{$$resmap[$i]};
				print "$$thing{id} res: x => $base_x + $x, y => $base_y + $y, res_index => $i\n" if $debug;
				push @resonances, { x => $base_x + $x, y => $base_y + $y, res_index => $i };
			}
		}
		else {
			print "No resmap returned; must have finished this item\n" if $debug;
			$$thing{state} = $WAITING;
			foreach my $cell (@{$$thing{cells}}) {
				$$cell{state} = $$thing{state};
			}
			delete $item_res{$$thing{id}};
		}
	}
	else {
		print "Unknown thing in update_resonances: $thing, $$thing{type}\n";
	}

	# add the standard elements for each res
	RES: foreach my $res (@resonances) {
		# check that the resonance is not in an exclusion
		ITEM: foreach my $id (keys %item_exclude) {
			# don't remove resonances because of the thing's own exclusions
			next if $id == $$thing{id};
			# if the thing is a wall or a roof, don't remove resonances because of
			# its room.
			if ( ($$thing{type} & ($WALL_GROUP | $MAP_WALL | $RESKEY_GROUP)) && $$thing{room}) {
				next if $id == ${$$thing{room}}{id};
			}
			# roofs, walls of buildings
			if ( ($$thing{type} & ($MAP_WALL | $RESKEY_GROUP)) && $$thing{building}) {
				next if $id == ${$$thing{building}}{id};
			}
			# ditto for columns and buildings; we could just say "next if column",
			# since columns shouldn't be anywhere near valid exclusions...
			if ($$thing{type} == $COLUMN) {
				next if $id == ${$$thing{building}}{id};
			}

			foreach my $rect_ref (@{$item_exclude{$id}}) {

				print "exclusion rect = $$rect_ref[0], $$rect_ref[1], $$rect_ref[2], $$rect_ref[3]\n" if $debug; 

				# check the cell's location; cells in exclusions don't have any resonances,
				# in case another cell moves onto it and builds while the 1st cell is still
				# supposed to be excluded.
				if ($$thing{type} == $CELL && 
					rectangles_intersect($rect_ref, [ $$thing{x},$$thing{y},$$thing{x},$$thing{y} ])) {
					print "No resonances for cell inside exclusion; $$thing{id} at $$thing{x},$$thing{y}\n" if $debug;
					last RES;
				}

				print "Omitting res($$res{x},$$res{y}) for item $$thing{id} because of item $id\n"
					if rectangles_intersect($rect_ref, [ $$res{x},$$res{y},$$res{x},$$res{y} ]) && $debug;
				next RES if rectangles_intersect($rect_ref, [ $$res{x},$$res{y},$$res{x},$$res{y} ]);
			}

		}

		$$res{pri} = $type_pri{$$thing{type}};
		$$res{thing} = $thing;
		$$res{type} = $RES;

		push @valid_resonances, $res;
	}

	# store the resonances in the item resonance hash
	$item_res{$$thing{id}} = \@valid_resonances;

}

sub 
prune_resonances($$) 
{
	my ($thing,$new_rect) = @_;

	# we've just changed an exclusion; go thru all the resonances
	# and remove any that impinge on the newly excluded area.

	# this could be optimised by having a grid-based index of items with
	# resonances in that grid. Divide the world into 8x8 (say) squares
	# and for each square (ie a hash keyed by grid x_y) store a hash
	# of item keys where those items have resonances in the square.
	# Checking which grid squares are affected by a given prune area
	# would be fairly easy, and we'd then just have to check those items
	# for resonance pruning.

	print "pruning resonances for $$thing{id}\n" if $debug;

	ITEM: foreach my $id (keys %item_res) {
		# don't prune the thing's own resonances
		next if $$thing{id} == $id;

		# if the thing is a room, don't remove resonances from the things in the
		# room.
		if ($$thing{type} == $ROOM) {
			foreach my $wall (@{$$thing{walls}}) {
				next ITEM if $id == $$wall{id};
			}
			foreach my $roof (@{$$thing{roofs}}) {
				next ITEM if $id == $$roof{id};
			}
			foreach my $pediment (@{$$thing{pediments}}) {
				next ITEM if $id == $$pediment{id};
			}
		}

		# have to be careful here otherwise the splice changes the list 
		# as we're deleting from it. Delete from the list in reverse
		# order to stop reshuffling hurting us.
		for (my $i = $#{$item_res{$id}}; $i >= 0; $i--) {
			my $res = ${$item_res{$id}}[$i];
			if (rectangles_intersect($new_rect, [ $$res{x},$$res{y},$$res{x},$$res{y} ])) {
				print "pruning res $i for $id at $$res{x}, $$res{y} because of $$thing{id}\n" if $debug;
				splice @{$item_res{$id}},$i,1;
			}
		}
	}
}

sub
get_res_score($$) 
{
	my ($thing, $res) = @_;

	my $score = 0;

	# bail out if this resonance belongs to this thing
	return 0 if $thing == $$res{thing};

	if ($$thing{type} == $CELL) {
		# my $range = sqrt(($$thing{x} - $$res{x})**2 + ($$thing{y} - $$res{y})**2);
		my $range = get_distance($thing, $res);
		# add 1 to avoid div 0
		$score = $$res{pri}/($range+1);
	}
	else {
		print "Unknown thing in get_res_score: $thing, $$thing{type}\n";
	}

	return $score;
}

sub
create($$) 
{
	my ($thing, $flags) = @_;
	$$thing{id} = ++$next_id;

	# default current ends for walls
	if (defined($$thing{final_end_1}) && defined($$thing{final_end_2})) {
		my $final_end_1 = $$thing{final_end_1};
		my $final_end_2 = $$thing{final_end_2};
		$$thing{end_1} = $final_end_1 + int(($final_end_2-$final_end_1)/2) + 1 unless defined($$thing{end_1});
		$$thing{end_2} = $final_end_1 + int(($final_end_2-$final_end_1)/2) unless defined($$thing{end_2});
	}

	# default heights for a resmap
	if (defined($$thing{resmap})) {
		$$thing{heights} = [ map (0,(0..$#{$$thing{resmap}})) ]
			unless defined($$thing{heights});
		$$thing{cells} = [];
	}

	# default stuff for a reskey (different resonance maps keyed by current layer)
	# or a resfunc (different resonance maps generated by function )
	if ($$thing{type} & $RESKEY_GROUP) {
		# calc the final height if a simple hash contains the resonance maps for each layer
		if (my $reskey = $$thing{reskey}) {
			$$thing{final_height} = scalar keys %$reskey
				unless defined($$thing{final_height});
		}
		$$thing{cells} = [];
		$$thing{layer} = 0;
		$$thing{filled_res} = [];
	}

	# create the tree list for this type if we have to
	$tree{$$thing{type}} = [] unless $tree{$$thing{type}};

	# add this thing to its tree list
	push @{$tree{$$thing{type}}}, $thing;

	# actions conditional on flags
	$active_item{$$thing{id}} = $thing if $flags & $FL_ACTIVE;
	update_resonances($thing) if $flags & $FL_RESONATE;

	return $thing;
}

sub
breed() 
{
	my $MAX_CELLS = 8;
	my $MAX_SEEK_CELLS = 15;
	# use ceil for 1 to n, int for 0 to n-1

	# cap on free cells
	my $seeking_cells = 0;
	foreach my $cell (@{$tree{$CELL}}) {
		$seeking_cells++ if $$cell{state} & $SEEKING_GROUP;
	}
	return if $seeking_cells > $MAX_SEEK_CELLS;

	my $new_cells = int(rand() * $MAX_CELLS);
	# print "$new_cells new cells\n";
	foreach (1..$new_cells) {
		my $cell = create({
			type => $CELL,
			nature => $CELL,
			x => int(rand() * $GX),
			y => int(rand() * $GY),
			z => 0,
			state => $SEEK,
			life => $lifespan{$CELL},
			},
			$FL_ACTIVE | $FL_RESONATE);
		print "New cell $$cell{id} at $$cell{x}, $$cell{y}\n" if $debug;
	}
}

sub
add_new_wall($) 
{
	my $wall = shift;

	print "wall $$wall{id} created from $$wall{end_1} to $$wall{end_2} on $$wall{line}, horiz $$wall{horiz}\n" if $debug;
	# add the new thing to the system lists
	update_resonances($wall);

	# walls which are added to complete a room are never active and
	# the room's exclusion zone covers them.
	if ($$wall{state} == $BUILD) {
		$active_item{$$wall{id}} = $wall;
		# add the exclusions
		my $exclusion_rect = $$wall{horiz}
			? [ $$wall{end_1}-1,$$wall{line}-1, $$wall{end_2}+1, $$wall{line}+1 ]
			: [ $$wall{line}-1,$$wall{end_1}-1, $$wall{line}+1, $$wall{end_2}+1 ];
		$item_exclude{$$wall{id}} = [ $exclusion_rect ] ;
		prune_resonances($wall, $exclusion_rect);
	}

}

sub
create_building(@)
{
	my ($building_rect, $grid_size, $point, $x_grid, $y_grid) = @_;
#	my $debug = 1;

	my $building = create({
		type => $BUILDING,
		state => $BUILD,
		rect => $building_rect,
		columns => [],
		walls => [],
		size => $grid_size,
		height => $grid_size * 2 + 2,
		points => $point,
		column_size => $column_size{$grid_size},
		}, $FL_ACTIVE);
	$item_exclude{$$building{id}} = [ $building_rect ];
	prune_resonances($building, $building_rect);

	# work out the column spacing...
	my ($min_grid, $max_grid) = (($x_grid > $y_grid) ? ($y_grid, $x_grid) : ($x_grid, $y_grid));
	print "min_grid, max_grid = $min_grid, $max_grid\n" if $debug;
	# initialise this to the existing points list in case we don't find a valid column spacing
	my $column_points = $point;
	foreach my $min_grid_factor (4,3,2,1) {
		print "mgf = $min_grid_factor\n" if $debug;
		# skip unless exact factor
		if ($min_grid % $min_grid_factor) {
			print "mgf not exact factor of $min_grid\n" if $debug;
			next;
		}
		my $column_grid = $min_grid / $min_grid_factor;
		# skip if we're too small
		if ($column_grid < $column_wall_min{$$building{column_size}}) {
			print "cg $column_grid too small\n" if $debug;
			next;
		}
		# skip unless the column spacing works for the max grid as well
		if ($max_grid % $column_grid) {
			print "cg $column_grid not exact factor of $max_grid\n" if $debug;
			next;
		}
		print "column_grid = $column_grid\n" if $debug;
		# create new points with $column_grid spacing
		$column_points = [];
		foreach my $p (0 .. $#$point) {
			my ($x,$y) = @{$$point[$p]};
			# add the current point
			push @$column_points, [ $x, $y ];
			my ($next_x,$next_y) = @{$$point[($p + 1) % ($#$point+1)]};
			if ($next_x != $x) {
				my $signed_grid_inc = $next_x > $x ? $column_grid : -$column_grid;
				my $nbr_new_points = abs($next_x - $x) / $column_grid - 1;
				foreach (1 .. $nbr_new_points) {
					print "Add new column point at $x + $signed_grid_inc * $_, $y\n" if $debug;
					push @$column_points, [ $x + $signed_grid_inc * $_, $y ];
				}
			}
			else {
				my $signed_grid_inc = $next_y > $y ? $column_grid : -$column_grid;
				my $nbr_new_points = abs($next_y - $y) / $column_grid - 1;
				foreach (1 .. $nbr_new_points) {
					print "Add new column point at $x, $y + $signed_grid_inc * $_\n" if $debug;
					push @$column_points, [ $x, $y + $signed_grid_inc * $_ ];
				}
			}
		}
		last;
	}

	# create a column for each offset
	my $prev_dir = get_direction($$column_points[$#$column_points], $$column_points[0]);
	foreach my $p (0 .. $#$column_points) {
		# save column position & facing info for buttresses
		my $next_dir = get_direction($$column_points[$p], $$column_points[($p+1) % ($#$column_points+1)]);
		my $column_position;
		if ($prev_dir == $next_dir) {
			$column_position = $CP_WALL;
		}
		else {
			my $diff = $next_dir - $prev_dir;
			$column_position = ($diff == 1 || $diff == -3) ? $CP_OUTSIDE_CORNER : $CP_INSIDE_CORNER;
		}

		my ($x,$y) = @{$$column_points[$p]};

		# we have smaller columns along straight runs
		my $col_size = $column_position == $CP_OUTSIDE_CORNER
			? $column_size{$grid_size}
			: $column_size{$grid_size - 2};
		print "col pos = $column_position, gs = $grid_size, cs = $col_size\n" if $debug;

		my $column = create({
			type => $COLUMN,
			size => $col_size,
			state => $COMPLETING,
			x => $x,
			y => $y,
			building => $building,
			cells => [],
			resmap => $column_res_map{$col_size},
			final_height => $$building{height},
			facing => $next_dir,
			column_position => $column_position,
			base => 0,
		},$FL_RESONATE);

		push @{$$building{columns}}, $column;

		$prev_dir = $next_dir;
	}

	# create a wall for each offset, now that we have all the columns and so can
	# work out the distances; columns may be different sizes...
	foreach my $p (0 .. $#$column_points) {
		# this column
		my ($x,$y) = @{$$column_points[$p]};
		my $column = ${$$building{columns}}[$p];
		# next column
		my $next_p = ($p + 1) % ($#$column_points+1);
		my ($next_x,$next_y) = @{$$column_points[$next_p]};
		my $next_column = ${$$building{columns}}[$next_p];

		my $resmap = [];
		my $first_increment = $$column{size} > 1 ? 2 : 1;
		my $second_increment = $$next_column{size} > 1 ? 2 : 1;
		if ($next_x != $x) {
			my $inc = $next_x > $x ? 1 : -1;
			my $nbr_points = abs($next_x - $x) - ($first_increment + $second_increment) + 1;
			my $res_x = $first_increment * $inc; 
			foreach (1 .. $nbr_points) {
				push @$resmap, [ $res_x, 0 ];
				$res_x += $inc;
			}
		}
		else {
			my $inc = $next_y > $y ? 1 : -1;
			my $nbr_points = abs($next_y - $y) - ($first_increment + $second_increment) + 1;
			my $res_y = $first_increment * $inc; 
			foreach (1 .. $nbr_points) {
				push @$resmap, [ 0, $res_y ];
				$res_y += $inc;
			}
		}

		my $wall = create({
			type => $MAP_WALL,
			state => $COMPLETING,
			x => $x,
			y => $y,
			resmap => $resmap,
			building => $building,
			cells => [],
			base => 0,
			final_height => $$building{height},
			},$FL_RESONATE);
		push @{$$building{walls}}, $wall;
		print "Created building wall from $x,$y to $next_x,$next_y\n" if $debug;
	}

	return $building;
}

sub
build($$) 
{
	my ($existing_thing, $new_part) = @_;

	if ($$existing_thing{type} == $CELL) {
		if ($$new_part{type} != $CELL) {
			print "Something other than a cell ($$new_part{type}) is building onto a cell\n";
			return;
		}
		# ok, two cells are joining; a wall, corner, column, door,...?
		my $type = $WALL;
		# find out which cell is the top or left one
		my ($first_cell, $second_cell, $len, $horiz);
		if ($$existing_thing{x} == $$new_part{x}) {
			# vertical wall
			$first_cell = $$existing_thing{y} < $$new_part{y} ? $existing_thing : $new_part;
			$second_cell = $$existing_thing{y} < $$new_part{y} ? $new_part : $existing_thing;
			$len = $$second_cell{y} - $$first_cell{y} + 1;
			$horiz = 0;
		}
		else {
			# horiz wall
			$first_cell = $$existing_thing{x} < $$new_part{x} ? $existing_thing : $new_part;
			$second_cell = $$existing_thing{x} < $$new_part{x} ? $new_part : $existing_thing;
			$len = $$second_cell{x} - $$first_cell{x} + 1;
			$horiz = 1;
		}

		# create the new thing
		my $new_thing = create({
			type => $type,
			state => $BUILD,
			life => $lifespan{$type},
			end_1 => $horiz ? $$first_cell{x} : $$first_cell{y},
			end_2 => $horiz ? $$second_cell{x} : $$second_cell{y},
			line => $horiz ? $$first_cell{y} : $$first_cell{x},
			cells => [ $first_cell, $second_cell ],
			len => $len,
			horiz => $horiz,
			height => 0,
			base => 0,
			},0);

		# shut down the cells
		foreach my $cell ($existing_thing, $new_part) {
			$$cell{state} = $BUILD;
			# don't try to move these cells
			delete $active_item{$$cell{id}};
			# take the resonances for these cells off the list
			delete $item_res{$$cell{id}};
			$$cell{nature} = $WALL;
			$$cell{horiz} = $horiz;
			$$cell{object} = $new_thing;
		}

		add_new_wall($new_thing);

	}
	elsif ($$existing_thing{type} & $WALL_GROUP) {
		if ($$new_part{type} == $CELL) {
			# adjust wall; change the relevant end and add the cell to the wall's list
			if ($$existing_thing{horiz}) {
				if ($$new_part{x} == $$existing_thing{end_1}-1) {
					# new end 1
					$$existing_thing{end_1}--;
				}
				elsif ($$new_part{x} == $$existing_thing{end_2}+1) {
					# new end 2
					$$existing_thing{end_2}++;
				}
				else {
					print "Cell is joining a vertical wall/roof but not at an end\n";
					return;
				}
			}
			else {
				if ($$new_part{y} == $$existing_thing{end_1}-1) {
					# new end 1
					$$existing_thing{end_1}--;
				}
				elsif ($$new_part{y} == $$existing_thing{end_2}+1) {
					# new end 2
					$$existing_thing{end_2}++;
				}
				else {
					print "Cell is joining a vertical wall/roof but not at an end\n";
				}
			}
			# adjust other wall data
			push @{$$existing_thing{cells}}, $new_part;
			$$existing_thing{len}++;

			# adjust cell state & remove from lists
			$$new_part{state} = $$existing_thing{state};
			$$new_part{nature} = $$existing_thing{type};
			$$new_part{horiz} = $$existing_thing{horiz};
			$$new_part{angle} = $$existing_thing{angle} if $$existing_thing{type} == $ROOF;
			$$new_part{tile_shape} = $$existing_thing{tile_shape} if $$existing_thing{type} == $ROOF;
			$$new_part{z} = $$existing_thing{base} + $$existing_thing{height};
			$$new_part{object} = $existing_thing;
			delete $active_item{$$new_part{id}};
			delete $item_res{$$new_part{id}};

			# check if the wall was completed by this cell
			if ($$existing_thing{state} == $COMPLETING
				&& $$existing_thing{len} == $$existing_thing{final_end_2} - $$existing_thing{final_end_1} + 1)
			{
				print "Completed a line for wall/roof $$existing_thing{id}, state $$existing_thing{state}",
					", height $$existing_thing{height}, final height $$existing_thing{final_height}\n" if $debug;
				$$existing_thing{height}++;
				if ($$existing_thing{height} == $$existing_thing{final_height}) {
					# change the state of the wall to WAITING, ie for the rest of
					# the room. Do the same for the cells in the wall.
					$$existing_thing{state} = $WAITING;
					foreach my $cell (@{$$existing_thing{cells}}) {
						$$cell{state} = $$existing_thing{state};
					}
					delete $item_res{$$existing_thing{id}};
				}
				else {
					if ($$existing_thing{type} == $PEDIMENT) {
						$$existing_thing{final_end_1}++;
						$$existing_thing{final_end_2}--;
					}
					# just finished a row, build the next one
					# new resonances are in middle of wall
					$$existing_thing{end_1} = $$existing_thing{final_end_1}
						+ int(($$existing_thing{final_end_2}-$$existing_thing{final_end_1})/2) + 1;
					$$existing_thing{end_2} = $$existing_thing{final_end_1}
						+ int(($$existing_thing{final_end_2}-$$existing_thing{final_end_1})/2);
					$$existing_thing{len} = 0;
				}
			}
			elsif ($$existing_thing{state} == $BUILD) {
				# update the exclusions; the room exclusions take care of COMPLETING
				# walls.
				delete $item_exclude{$$existing_thing{id}};
				my $exclusion_rect = $$existing_thing{horiz}
						? [ $$existing_thing{end_1}-1,$$existing_thing{line}-1, 
							$$existing_thing{end_2}+1, $$existing_thing{line}+1 ]
						: [ $$existing_thing{line}-1,$$existing_thing{end_1}-1, 
							$$existing_thing{line}+1, $$existing_thing{end_2}+1 ];
				$item_exclude{$$existing_thing{id}} = [ $exclusion_rect ];
				prune_resonances($existing_thing, $exclusion_rect);
			}

			update_resonances($existing_thing) unless $$existing_thing{state} == $WAITING;
		}
		elsif ($$new_part{type} == $WALL) {
			# two parallel walls are building together to make a room.
			# the current extents of the pair define the final size.
			my $room_rect = [];
			if ($$new_part{horiz}) {
				$$room_rect[0] = min($$existing_thing{end_1}, $$new_part{end_1});
				$$room_rect[1] = min($$existing_thing{line}, $$new_part{line});
				$$room_rect[2] = max($$existing_thing{end_2}, $$new_part{end_2});
				$$room_rect[3] = max($$existing_thing{line}, $$new_part{line});
			}
			else {
				$$room_rect[0] = min($$existing_thing{line}, $$new_part{line});
				$$room_rect[1] = min($$existing_thing{end_1}, $$new_part{end_1});
				$$room_rect[2] = max($$existing_thing{line}, $$new_part{line});
				$$room_rect[3] = max($$existing_thing{end_2}, $$new_part{end_2});
			}

			# check that the proposed room doesn't impinge on any existing exclusion zones
			foreach my $id (keys %item_exclude) {
				# ignore exclusions for the two walls
				next if $id == $$existing_thing{id} || $id == $$new_part{id};
				foreach my $excl_rect (@{$item_exclude{$id}}) {
					return if rectangles_intersect($room_rect, $excl_rect);
				}
			}

			# wall height
			my $height = int((($$room_rect[2] - $$room_rect[0])+($$room_rect[3]-$$room_rect[1])/2)
				* ((3 + rand() * 4)/10));

			# create the new room
			my $new_thing = create({
				type => $ROOM,
				state => $BUILD,
				rect => $room_rect,
				height => $height,
				x => $$room_rect[0] + int(($$room_rect[2] - $$room_rect[0])/2),
				y => $$room_rect[1] + int(($$room_rect[3] - $$room_rect[1])/2),
				},$FL_ACTIVE);

			print "New room $$new_thing{id} from walls $$existing_thing{id} and $$new_part{id} , rect = @$room_rect, life = $$new_thing{life}\n" if $debug;

			# create the new walls for the room
			my @new_walls = ();
			foreach my $i (0..1) {
				my ($x, $y, $resmap);
				if ($$new_part{horiz}) {
					my $final_end_1 = $$room_rect[1] + 1;
					my $final_end_2 = $$room_rect[3] - 1;
					$x = $$room_rect[0 + 2 * $i];
					$y = $final_end_1 + int (($final_end_2 - $final_end_1 + 1)/2);
					$resmap = [ map [ 0, $_ - $y ], ($final_end_1 .. $final_end_2) ];
				}
				else {
					my $final_end_1 = $$room_rect[0] + 1;
					my $final_end_2 = $$room_rect[2] - 1;
					$x = $final_end_1 + int (($final_end_2 - $final_end_1 + 1)/2);
					$y = $$room_rect[1 + 2 * $i];
					$resmap = [ map [ $_ - $x, 0 ], ($final_end_1 .. $final_end_2) ];
				}

				my $new_wall = create({
					type => $MAP_WALL,
					state => $COMPLETING,
					x => $x,
					y => $y,
					resmap => $resmap,
					life => $lifespan{$WALL},
					room => $new_thing,
					cells => [],
					base => 0,
					final_height => $height,
					},0);

				print "New map wall $$new_wall{id} at $x,$y, horiz ! $$new_part{horiz}\n" if $debug;
				if ($debug) {
					foreach my $list_ref (@$resmap) {
						my ($x,$y) = @$list_ref;
						print "\t$x,$y\n";
					} 
				}

				push @new_walls, $new_wall;
			}

			# add the walls list to the room; they refer to each other, so we have
			# to do one creation first & then update the ref.
			$$new_thing{walls} = [ $existing_thing, $new_part, @new_walls ];

			# don't do this until the room knows about all its walls, otherwise
			# the walls inhibit each other's resonances.
			update_resonances($new_walls[0]);
			update_resonances($new_walls[1]);

			# do actions common to both existing walls
			foreach my $wall ($existing_thing, $new_part) {

				$$wall{room} = $new_thing;
				$$wall{final_end_1} = $$wall{horiz} ? $$room_rect[0] : $$room_rect[1];
				$$wall{final_end_2} = $$wall{horiz} ? $$room_rect[2] : $$room_rect[3];
				$$wall{final_height} = $height;
				$$wall{state} = $COMPLETING;

				# has the wall finished its first row already?
				if (($$wall{end_1} == $$wall{final_end_1} && $$wall{end_2} == $$wall{final_end_2})) {
					$$wall{height} = 1;
					if ($$wall{height} == $$wall{final_height}) {
						print "wall $$wall{id} waiting straight away\n" if $debug;
						$$wall{state} = $WAITING;
						delete $item_res{$$wall{id}};
					}
					else {
						# new resonances are in middle of wall
						$$wall{end_1} = $$wall{final_end_1} + int(($$wall{final_end_2}-$$wall{final_end_1})/2) + 1;
						$$wall{end_2} = $$wall{final_end_1} + int(($$wall{final_end_2}-$$wall{final_end_1})/2);
						$$wall{len} = 0;
					}
				}
				else {
					$$wall{height} = 0;
				}

				# set the cells to the wall's state
				foreach my $cell (@{$$wall{cells}}) {
					$$cell{state} = $$wall{state};
				}

				update_resonances($wall) unless $$wall{state} == $WAITING;
				# remove the walls from the active list (they aren't looking for 
				# other walls any more).
				delete $active_item{$$wall{id}};
				# remove the exclusions, since the room exclusions will handle the area.
				delete $item_exclude{$$wall{id}};
			}

			my $exclusion_rect = [ $$room_rect[0]-2, $$room_rect[1]-2, $$room_rect[2]+2, $$room_rect[3]+2];
			$item_exclude{$$new_thing{id}} = [ $exclusion_rect ];
			prune_resonances($new_thing, $exclusion_rect);
		}
		else {
			print "Thing $$new_part{id} with unexpected type ($$new_part{type}) is building onto wall or roof $$existing_thing{id}\n";
			return;
		}
	}
	elsif ($$existing_thing{type} & $MAP_GROUP) {
		if ($$new_part{type} == $CELL) {
			# find the index in the resmap of the resonance this cell has joined;
			# the offset from the cell position to the object origin will be the same as
			# the resmap entry.

=for comment
			my $cell_offset_x = $$new_part{x} - $$existing_thing{x};
			my $cell_offset_y = $$new_part{y} - $$existing_thing{y};
			my $index = 0;
			foreach my $res (@{$$existing_thing{resmap}}) {
				my ($x,$y) = @$res;
				last if $x == $cell_offset_x && $y == $cell_offset_y;
				$index++;
			}
=cut

			# when the cell joins the resonance, the resonance index is added to the cell
			my $index = $$new_part{res_index};
			if (!defined($index) || $index > $#{$$existing_thing{resmap}}) {
				print "Couldn't find matching res for cell\n";
				return;
			}

			print "Cell $$new_part{id} joining map object $$existing_thing{id} at res $index\n" if $debug;

			# adjust cell state & remove from lists
			$$new_part{state} = $$existing_thing{state};
			$$new_part{nature} = $$existing_thing{type};
			$$new_part{z} = $$existing_thing{base} + ${$$existing_thing{heights}}[$index];
			$$new_part{object} = $existing_thing;
			delete $active_item{$$new_part{id}};
			delete $item_res{$$new_part{id}};

			# adjust other column/wall data
			push @{$$existing_thing{cells}}, $new_part;
			${$$existing_thing{heights}}[$index]++;

			# check if the stack was completed by this cell
			if (${$$existing_thing{heights}}[$index] == $$existing_thing{final_height}) {
				print "Completed a stack for column/wall $$existing_thing{id}, state $$existing_thing{state}",
					", height ${$$existing_thing{heights}}[$index], final height $$existing_thing{final_height}\n" if $debug;

				# check if all the stacks in the thing are now done
				my $short_stack = 0;
				foreach my $stack_height (@{$$existing_thing{heights}}) {
					$short_stack = $stack_height < $$existing_thing{final_height};
					last if $short_stack;
				}

				if (! $short_stack) {
					# change the state of the thing to WAITING, ie for the rest of
					# the building/room. Do the same for the cells.
					$$existing_thing{state} = $WAITING;
					foreach my $cell (@{$$existing_thing{cells}}) {
						$$cell{state} = $$existing_thing{state};
					}
					delete $item_res{$$existing_thing{id}};
				}
				else {
					# we finished one stack so take off its resonance
					update_resonances($existing_thing);
				}
			}

		} # cell joining map thing
		else {
			print "Unknown thing joining map object: $$new_part{id}\n";
		}
	} # something joining map thing
	elsif ($$existing_thing{type} & $RESKEY_GROUP) {
		if ($$new_part{type} == $CELL) {

			# find the current resmap for the object; either by a function or a hash lookup
			my $resmap = $$existing_thing{resfunc}
				?  &{$$existing_thing{resfunc}}($existing_thing)
				: ${$$existing_thing{reskey}}{$$existing_thing{layer}};

			# when the cell joins the resonance, the resonance index is added to the cell
			my $index = $$new_part{res_index};
			if (!defined($index) || $index > $#$resmap) {
				print "Couldn't find matching res for cell\n";
				return;
			}
			my $attribs = ${$$resmap[$index]}[2];

			print "Cell $$new_part{id} joining map key object $$existing_thing{id} at res $index\n" if $debug;

			# adjust cell state & remove from lists
			$$new_part{state} = $$existing_thing{state};
			$$new_part{nature} = $$existing_thing{type};
			$$new_part{z} = $$existing_thing{base} + $$existing_thing{layer};
			$$new_part{object} = $existing_thing;
			foreach my $attrib (%$attribs) {
				$$new_part{$attrib} = $$attribs{$attrib};
			}
			delete $active_item{$$new_part{id}};
			delete $item_res{$$new_part{id}};

			# adjust other column/wall data
			push @{$$existing_thing{cells}}, $new_part;
			${$$existing_thing{filled_res}}[$index] = 1;

			# check if the layer was completed by this cell
			for ($index=0; $index <= $#$resmap; $index++) {
				last unless ${$$existing_thing{filled_res}}[$index];
			}
			if ($index > $#$resmap) {
				print "Completed layer $$existing_thing{layer} for reskey object $$existing_thing{id}",
					", state $$existing_thing{state}" if $debug;
				print ", final height $$existing_thing{final_height}\n" if $$existing_thing{final_height} && $debug;
				print "\n" if $debug;

				$$existing_thing{layer}++;

				# check if this was the final layer
				if ($$existing_thing{final_height} && $$existing_thing{layer} == $$existing_thing{final_height}) {
					# change the state of the thing to WAITING, ie for the rest of
					# the building/room. Do the same for the cells.
					$$existing_thing{state} = $WAITING;
					foreach my $cell (@{$$existing_thing{cells}}) {
						$$cell{state} = $$existing_thing{state};
					}
					delete $item_res{$$existing_thing{id}};
				}
				else {
					# clear filled resonance list
					$$existing_thing{filled_res} = [];
				}
			}

			# we have to update the resonances for every cell joining a layer
			update_resonances($existing_thing) unless $$existing_thing{state} == $WAITING;

		} # cell joining reskey thing
		else {
			print "Unknown thing joining reskey object: $$new_part{id}\n";
		}
	} # something joining reskey thing
	else {
		print "Unknown thing in build: $$existing_thing{id}\n";
	}

}

sub
find_best_spot($) 
{
	my $active_cell = shift;
	my $best_res = undef;
	my $best_score = 0;
	my $debug = 0;

	# all types of objects have a number of resonant locations,
	# each of which may have a different priority. For example,
	# extending an incomplete wall may have a higher priority than
	# starting a parallel wall. 

	# We find the "best" spot to move to based on range and
	# priority; we take priority/range to find each spot's score.
	print "Res scores for cell $$active_cell{id}:" if $debug;
	foreach my $resonant_item_id (keys %item_res) {
		print " id $resonant_item_id => (" if $debug;
		my $res_list_ref = $item_res{$resonant_item_id};
		foreach my $res (@$res_list_ref) {
			next unless $res;
			next if $active_cell == $$res{thing};
			my $score = get_res_score($active_cell, $res);
			print " $score" if $debug;
			if ($score > $best_score) {
				print "*" if $debug;
				$best_score = $score;
				$best_res = $res;
			}
		}
		print ")" if $debug;
	}

	if ($best_score) {

		print "Best resonance for $$active_cell{id} is at $$best_res{x}, $$best_res{y}\n" if $debug;
		# adjust the cell's position towards the resonance if necessary
		$$active_cell{x}++ if $$active_cell{x} < $$best_res{x};
		$$active_cell{x}-- if $$active_cell{x} > $$best_res{x};
		$$active_cell{y}++ if $$active_cell{y} < $$best_res{y};
		$$active_cell{y}-- if $$active_cell{y} > $$best_res{y};

		# did we get to the resonance?
		if ($$active_cell{x} == $$best_res{x} && $$active_cell{y} == $$best_res{y}) {
			# if this resonance has an index, set it in the cell
			$$active_cell{res_index} = $$best_res{res_index} if defined($$best_res{res_index});
			# the active cell should now be joined to whatever owned
			# the resonance
			build($$best_res{thing}, $active_cell);
		}
		else {
			print "cell $$active_cell{id} moved to $$active_cell{x},$$active_cell{y}\n" if $debug;
			update_resonances($active_cell) if $$active_cell{state} == $SEEK;
		}
	}
	else {
		print "No resonance for $$active_cell{id}\n" if $debug;
	}

}

# recursive use requires prototype
sub dissolve($$);
sub
dissolve($$)
{
	my ($thing, $cell_state) = @_;

	# we may get called on the same thing twice
	return if $$thing{state} == $DEAD;

	$$thing{state} = $DEAD;

	# don't care if these exist or not
	delete $active_item{$$thing{id}};
	delete $item_res{$$thing{id}};
	delete $item_exclude{$$thing{id}};

	if ($$thing{cells}) {
		foreach my $cell (@{$$thing{cells}}) {
			$$cell{state} = $cell_state;
			$active_item{$$cell{id}} = $cell if $cell_state == $JOIN;
		}
		$$thing{cells} = [];
	}
	elsif ($$thing{type} == $ROOM) {
		foreach my $component (@{$$thing{walls}},@{$$thing{roofs}},@{$$thing{pediments}}) {
			dissolve($component,$cell_state);
		}
	}
	else {
		print "Unexpected thing in dissolve: $$thing{id}\n";
	}
}

# recursive use requires prototype
sub ncr(@);
sub
ncr(@)
{
	my $nbr_in_comb = shift;
	my @values = @_;
	my @combos = ();

	# the routine is failsafe (returns empty list) for values of N greater than the listsize;
	# make it safe for low values also.
	return ( [] ) if $nbr_in_comb <= 0;

	foreach my $val_indx (0 .. $#values - ($nbr_in_comb - 1)) {
		my $val = shift @values;
		if ($nbr_in_comb == 1) {
			push @combos, [ $val ];
		}
		else {
			foreach my $combo_ref (ncr($nbr_in_comb-1,@values)) {
				unshift @$combo_ref, $val;
				push @combos, $combo_ref;
			}
		}
	}

	return @combos;
}

sub
search() 
{

	my $thing;
	THING: foreach my $id (sort numeric keys %active_item) {
		# check the thing we get is still active; it may have joined with a
		# previous thing in this search.
		my $thing = $active_item{$id} or next;
		print "Found a dead thing in active list\n" if $$thing{state} == $DEAD;

		if ($$thing{type} == $CELL) {

			if ($$thing{life}-- == 0) {
				$$thing{state} = $DEAD;
				delete $active_item{$id};
				delete $item_res{$id};
				next THING;
			}

			find_best_spot($thing);
		}
		elsif ($$thing{type} == $WALL) {

			if ($$thing{life}-- == 0) {
				print "Wall $$thing{id} has died\n" if $debug;
				# this wall has run out of time to find a pair; kill it and all
				# its cells.
				dissolve($thing,$DEAD);
				# we have to update the resonances for everything else, since
				# they may have been inhibited by the exclusions of this wall.
				# Don't need to do anything higher than walls (rooms, roofs, map_walls, etc)
				# since they can't have overlapping exclusions.
				foreach my $cell (@{$tree{$CELL}}) {
					update_resonances($cell) if $$cell{state} == $SEEK;
				}
				foreach my $wall (@{$tree{$WALL}}) {
					update_resonances($wall) if $$wall{state} & ($BUILD | $COMPLETING);
				}
				next THING;
			}

			my $WALL_REACH = 1.5;
			my $MIN_WALL_SEP = 4;
			foreach my $other_wall (@{$tree{$WALL}}) {

				# checks before we see how close it is

				# not the same wall and not part of something already
				next if $thing == $other_wall || $$other_wall{state} != $BUILD;
				# same direction
				next unless $$thing{horiz} == $$other_wall{horiz};
				# not too close together
				next if abs($$thing{line} - $$other_wall{line}) < $MIN_WALL_SEP;

				my $distance = get_distance($thing, $other_wall);
				if ($distance < $$thing{len} * $WALL_REACH) {
					build($thing, $other_wall);
					next THING;
				}
			}

		}
		elsif ($$thing{type} == $ROOM) {

#			my $debug = 1;

			if ($$thing{state} == $BUILD) {
				# check if initial walls are finished
				foreach my $wall (@{$$thing{walls}}) {
					next THING if $$wall{state} != $WAITING;
				}
				# all walls are waiting, so the room is finished.
				print "Room $$thing{id} has walls, roofing\n" if $debug;
				$$thing{state} = $COMPLETING;

				my $rect = $$thing{rect};

				# pyramid style roof, ie slopes on all sides
				my $new_thing = create({
					type => $RESKEY_THING,
					state => $COMPLETING,
					room => $thing,
#					x => $$thing{x},
#					y => $$thing{y},
#					x_dim => $$rect[2] - $$rect[0] + 1,
#					y_dim => $$rect[3] - $$rect[1] + 1,
#					resfunc => \&pyramid_res_map,
					resfunc => \&single_peak_res_map,
					tile_color => 'red',
					x => $$rect[0],
					y => $$rect[1],
					base_points => [
						[ 0,0 ],
						[ $$rect[2] - $$rect[0], 0 ],
						[ $$rect[2] - $$rect[0], $$rect[3] - $$rect[1] ],
						[ 0, $$rect[3] - $$rect[1] ],
						],
					base => $$thing{height},
					},$FL_RESONATE);
				push @{$$thing{roofs}}, $new_thing;

			}
			elsif ($$thing{state} == $COMPLETING) {
				# check if roofs are finished
				foreach my $roof (@{$$thing{roofs}}) {
					next THING if $$roof{state} != $WAITING;
				}
				my $rect = $$thing{rect};
				# smaller rooms last longer, but put a floor under life so really big rooms stay a while
				$$thing{life} = max(1500, int($lifespan{$ROOM} * (200 /
					(($$rect[2] - $$rect[0])*($$rect[3]-$$rect[1]) * $$thing{height}))));
				print "Room $$thing{id} completed, rect = ( @$rect ), life = $$thing{life}\n" if $debug;
				$$thing{state} = $FINISHED;
			}
			elsif ($$thing{state} == $FINISHED) {

				if ($$thing{life}-- == 0) {
					print "Room $$thing{id} has died\n" if $debug;
					# this wall has run out of time to find a pair; kill it and free all
					# its cells.
					dissolve($thing,$JOIN);
					# we have to update the resonances for everything else, since
					# they may have been inhibited by the exclusions of this wall.
					# Don't need to do anything higher than walls (rooms, roofs,etc)
					# since they can't have overlapping exclusions.
					foreach my $cell (@{$tree{$CELL}}) {
						update_resonances($cell) if $$cell{state} == $SEEK;
					}
					foreach my $wall (@{$tree{$WALL}}) {
						update_resonances($wall) if $$wall{state} & ($BUILD | $COMPLETING);
					}
					next THING;
				}

				my $ROOM_REACH = 35;
				my $TARGET = 2500;
				my $ROOM_VALUE = 200;
				my $rect = $$thing{rect};
				my $score = $$thing{height} * ($$rect[2] - $$rect[0]) * ($$rect[3] - $$rect[1]);
				my @joining_list = ($thing);
				print "$$thing{id} is checking for other rooms, score = $score\n" if $debug;
				foreach my $other_room (@{$tree{$ROOM}}) {

					# checks before we see how close it is

					# not the same thing, ready for join
					next if $thing == $other_room || $$other_room{state} != $FINISHED;

					my $distance = get_distance($thing, $other_room);
					next if $distance > $ROOM_REACH;
					print "\tSees finished room $$other_room{id}\n" if $debug;
					push @joining_list, $other_room;
					my $other_rect = $$other_room{rect};
					$score += $ROOM_VALUE + $$other_room{height} 
						* ($$other_rect[2] - $$other_rect[0]) 
						* ($$other_rect[3] - $$other_rect[1]);
					print "\tNew score is $score\n" if $debug;
				}
				print "Final score is $score\n" if $debug;

				# we have to see if we can make the target while taking existing buildings into account
				my $best_score;

				if ($score >= $TARGET && $#joining_list > 1) {
					# we have a list of finished rooms to join together. We also want to
					# find all incomplete rooms and walls which impinge on the rectangle
					# encompassing the finished rooms. All these things will be knocked down
					# to free their cells for the building.

					# first check to see if this joining list differs from the previous one
					# for this building, which must have failed.
					if ($prev_joining_list{$$thing{id}}
						&& $#{$prev_joining_list{$$thing{id}}} == $#joining_list)
					{
						my @new_joining_list = @joining_list;
						my $change = 0;
						foreach my $thing (@{$prev_joining_list{$$thing{id}}}) {
							my $new_thing = shift @new_joining_list;
							$change = 1 && last if $new_thing != $thing;
						}
						if (! $change) {
							print "Joining list for $$thing{id} hasn't changed; don't bother\n" if $debug;
							next THING;
						}
					}
					$prev_joining_list{$$thing{id}} = [ @joining_list ];

					# we must ensure this building rectangle doesn't impinge on the exclusion
					# zone for other buildings. If it does, we prune the joining list until
					# it doesn't any more (but still makes the target)

					# the -2 in the next line means we will have at least three things in the
					# joining list after any skips.
					my @building_rect;
					foreach my $nbr_skips (0..min($#joining_list-2,2)) {

						$best_score = undef;
						my $best_skip_index = undef;

						# @skips contains a list of lists of thing refs, ie a list of skip lists
						my @skips = ncr($nbr_skips, @joining_list);

						print "nbr_skips = $nbr_skips, $#skips skip lists\n" if $debug;
						my $skip_index = 0;
						SKIPLIST: foreach my $skip_combo_ref (@skips) {
							if ($debug) {
								print "skip list:\n";
								foreach my $thing (@$skip_combo_ref) {
									print " $$thing{id}";
								}
								print "\n";
							}

							# find the bounds of the finished buildings;
							@building_rect = ($GX,$GY,-1,-1);
							my $score = 0;
							ROOM: foreach my $room (@joining_list) {

								# skip any rooms in the skip list
								foreach my $thing (@$skip_combo_ref) {
									print "Skipping $$room{id}\n" if $room == $thing && $debug;
									next ROOM if $room == $thing;
								}

								print "Bounds for room $$room{id} = @{$$room{rect}}\n" if $debug;
								foreach (0..1) {
									$building_rect[$_] = min($building_rect[$_], ${$$room{rect}}[$_]);
								}
								foreach (2..3) {
									$building_rect[$_] = max($building_rect[$_], ${$$room{rect}}[$_]);
								}
								my $rect = $$room{rect};
								$score += $ROOM_VALUE + $$room{height} 
									* ($$rect[2] - $$rect[0]) * ($$rect[3] - $$rect[1]);
							}
							print "Building rect = @building_rect\n" if $debug;

							# have we still made the target after skips
							if ($score < $TARGET) {
								print "Target not made after skips\n" if $debug;
								next; # next skip list
							}

							$best_score = 0 unless defined($best_score);

							# check that the new building doesn't conflict with any existing
							# buildings; this can happen if the candidate rooms are clustered
							# around one of the corners of the existing building.
							foreach my $building (@{$tree{$BUILDING}}) {
								if (rectangles_intersect(\@building_rect, $$building{rect})) {
									print "Clash with existing building $$building{id}\n" if $debug;
									next SKIPLIST;
								}
							}

							# valid skip list (makes target, doesn't clash with other buildings) so record it
							if ($score > $best_score) {
								print "New best score; old = $best_score, new = $score, i = $skip_index\n" if $debug;
								$best_score = $score;
								$best_skip_index = $skip_index;
							}
						} 
						continue {
							$skip_index++;
						} # SKIPLIST

						if (! defined($best_score)) {
							# we never even got to check building intersections, ie the
							# target was never made. Skipping more rooms won't help so bail.
							print "Target never reached, skip room\n" if $debug;
							last;
						}

						# did we find a combination that reached the score without clashing?
						if ($best_score > 0) {
							# yep.
							print "Found valid joining list; score = $best_score, skip# = $best_skip_index\n" if $debug;
							# we only need to care about skips if we actually have some;
							# otherwise, the existing joining_list is fine.
							if ($nbr_skips > 0) {
								# ok, build a new joining list (much easier than pruning old one)
								my $skip_list = $skips[$best_skip_index];
								my @new_joining_list = ();
								ROOM: foreach my $room (@joining_list) {
									# skip any rooms in the skip list
									foreach my $thing (@$skip_list) {
										print "New J list; skipping $$room{id}\n" if $room == $thing && $debug;
										next ROOM if $room == $thing;
									}
									# add the room to the new list
									push @new_joining_list, $room;
								}
								@joining_list = @new_joining_list;
							}

							# recalc the building rect with the final J list
							@building_rect = ($GX,$GY,-1,-1);
							foreach my $room (@joining_list) {
								print "Real building rect; new room $$room{id} @{$$room{rect}}\n" if $debug;
								foreach (0..1) {
									$building_rect[$_] = min($building_rect[$_], ${$$room{rect}}[$_]);
								}
								foreach (2..3) {
									$building_rect[$_] = max($building_rect[$_], ${$$room{rect}}[$_]);
								}
							}
							print "Real building rect; @building_rect\n" if $debug;

							# bail out of the skip loop; the minimum number of skips is what we want.
							last;
						}

					} # number of skips loop

					# did we find a valid list?
					if (!defined($best_score) || $best_score == 0) {
						# nope; bail on this room
						print "No valid list found after existing building check\n" if $debug;
						next;
					}

					# find the rooms/walls in that area; we may be adding rooms twice
					# but dissolve is smart enough to ignore dead things.
					foreach my $other_thing (@{$tree{$ROOM}}, @{$tree{$WALL}}) {
						# walls in non-build state will be included by their rooms
						next if $$other_thing{type} == $WALL && $$other_thing{state} != $BUILD;
						my $other_rect = $$other_thing{type} == $WALL
							? $$other_thing{horiz}
								? [ $$other_thing{end_1}, $$other_thing{line}, 
									$$other_thing{end_2}, $$other_thing{line} ] 
								: [ $$other_thing{line}, $$other_thing{end_1}, 
									$$other_thing{line}, $$other_thing{end_2} ] 
							: $$other_thing{rect};
						push @joining_list, $other_thing if rectangles_intersect(\@building_rect, $other_rect);
					}
					print "Final joining list", map (" $$_{id}", @joining_list), "\n" if $debug;

					# make a plan!
					my ($point, $width, $height) = make_plan;
					if ($debug) {
						print "plan of $width x $height\n";
						foreach (@$point) { my ($x,$y) = @$_; print "\t$x,$y\n"; }
					}

					my @grid_sizes = (10,8,6,4,2,0);
					my $grid_size;
					foreach (@grid_sizes) {
						$grid_size = $_;
						# bail out if the smallest grid didn't fit.
						last if $grid_size == 0;
						# fit the plan to our area and convert the unit points to real locations
						print "Checking grid size $grid_size in @building_rect\n" if $debug;
						last if fit_plan($point, $width, $height, $grid_size, \@building_rect);
					}

					if ($grid_size == 0) {
						print "Couldn't fit plan to area\n" if $debug;
						next;
					}

					# take the x & y grid sizes off the front of the point list
					my $x_grid = shift @$point;
					my $y_grid = shift @$point;

					if ($debug) {
						foreach (@$point) { my ($x,$y) = @$_; print "\t$x,$y\n"; }
					}

					# dissolve all the joining things; remove resonances,
					# exclusions, active items, and set all cells to join (ie seek without
					# resonating), and set the component states to DEAD.
					foreach (@joining_list) {
						dissolve($_,$JOIN);
					}

					# update all floating wall & cell resonances in case they were inhibited by something
					# we just killed. Anything in a room can't have inhibited resonances.
					foreach my $other_thing (@{$tree{$WALL}}, @{$tree{$CELL}}) {
						next if $$other_thing{type} == $WALL && $$other_thing{state} != $BUILD;
						next if $$other_thing{type} == $CELL && $$other_thing{state} != $SEEK;
						update_resonances($other_thing);
					}

					# create the building
					my $building = create_building(
						\@building_rect, $grid_size, $point, $x_grid, $y_grid);

					# turn refresh on
#					$refresh = 1;


				} # creating a building
			} # room finished
		} # room
		elsif ($$thing{type} == $BUILDING) {

#			my $debug=1;

			if ($$thing{state} == $BUILD) {
				# check if initial columns are finished
				foreach my $column (@{$$thing{columns}}) {
					next THING if $$column{state} != $WAITING;
				}
				foreach my $wall (@{$$thing{walls}}) {
					next THING if $$wall{state} != $WAITING;
				}

				# walls & columns complete; have we started buttresses yet? 
				unless ($$thing{buttresses}) {
					my $buttresses = $$thing{buttresses} = [ ];

					foreach my $column (@{$$thing{columns}}) {

						my $resfunc;
						if ($$column{size} == 1) {
							$resfunc = \&size_1_buttress_resmap;
						}
						elsif ($$column{size} == 2) {
							$resfunc = \&size_2_buttress_resmap;
						}
						elsif ($$column{size} == 3) {
							$resfunc = \&size_3_buttress_resmap;
						}
						else {
							die "No buttress resfunc for column size $$column{size}";
						}

						my $buttress = create({
							x => $$column{x},
							y => $$column{y},
							base => 0,
							type => $RESKEY_THING,
							state => $COMPLETING,
							tile_color => 'red',
							column => $column,
							resfunc => $resfunc,
							building => $thing,
							},$FL_RESONATE);
						push @$buttresses, $buttress;
					}

					next THING;
				}

				# check buttress progress; we'll go straight thru if none created
				foreach my $buttress (@{$$thing{buttresses}}) {
					next THING if $$buttress{state} != $WAITING;
				}

				# all walls done, so build the roof
				print "Building $$thing{id} has walls, roofing\n" if $debug;
				$$thing{state} = $COMPLETING;

				# have to create the roof points before we call create so we can
				# grow them (if needed).
				my $roof_points = [ @{$$thing{points}} ];
				print "Growing points\n" if $debug && $$thing{column_size} > 1;
				resize_points(1,$roof_points) if $$thing{column_size} > 1;

				my $roof = create({
					type => $RESKEY_THING,
					state => $COMPLETING,
					x => 0,
					y => 0,
					resfunc => \&single_peak_gable_res_map,
					tile_color => 'blue',
					no_shared_gables => 1,
					base_points => $roof_points,
					base => $$thing{height},
					building => $thing,
					},$FL_RESONATE);
				$$thing{roofs} = [ $roof ];

			}
			elsif ($$thing{state} == $COMPLETING) {
				# check if roofs are finished
				foreach my $roof (@{$$thing{roofs}}) {
					next THING if $$roof{state} != $WAITING;
				}
				print "Building $$thing{id} completed\n" if $debug;
				$$thing{state} = $FINISHED;
			}
		}
		else {
			print "Unknown type of thing (id $id, $$thing{type}) in active item\n";
		}
	}
}

sub
report() 
{
	print "\n", "*" x 80, "\nReport; gen $gen, $next_id items created\n";
	print "Cell count: ", scalar(@{$tree{$CELL}}), "\n";
	print "Wall count: ", scalar(@{$tree{$WALL}}), " -> ";
	foreach my $wall (@{$tree{$WALL}}) { print " $$wall{id}"; } print "\n";
	print "Room count: ", scalar(@{$tree{$ROOM}}), " -> ";
	foreach my $room (@{$tree{$ROOM}}) { print " $$room{id}"; } print "\n";
	if ($tree{$ROOF}) {
		print "Roof count: ", scalar(@{$tree{$ROOF}}), " -> ";
		foreach my $roof (@{$tree{$ROOF}}) { print " $$roof{id}"; } print "\n";
	}

	my %type_total;
	print "Resonant items: ", scalar keys %item_res, " -> ";
	foreach my $id (sort numeric keys %item_res) {
		print " $id";
		my $thing = undef;
		THING: foreach (sort numeric keys %tree) {
			foreach my $tree_thing (@{$tree{$_}}) {
				if ($id == $$tree_thing{id}) {
					$thing = $tree_thing;
					last THING;
				}
			}
		}
		$type_total{$$thing{type}}++ if ($thing);
	}
	print "\n";
	foreach (sort numeric keys %type_total) {
		print "\t$_ = $type_total{$_}\n";
	}

	print "Active items: ", scalar keys %active_item, " -> ";
	%type_total = ();
	foreach my $id (sort numeric keys %active_item) {
		print " $id";
		my $thing = undef;
		THING: foreach (sort numeric keys %tree) {
			foreach my $tree_thing (@{$tree{$_}}) {
				if ($id == $$tree_thing{id}) {
					$thing = $tree_thing;
					last THING;
				}
			}
		}
		$type_total{$$thing{type}}++ if ($thing);
	}
	print "\n";
	foreach (sort numeric keys %type_total) {
		print "\t$_ = $type_total{$_}\n";
	}

	print "Excluding items: ", scalar keys %item_exclude, " -> ";
	foreach (sort numeric keys %item_exclude) { print " $_"; } print "\n";
	print "*" x 80, "\n\n";
	render_tk_3d(1);
}

sub 
inspect_selection($) 
{
	my $entry = shift;

	if ($entry->selectionPresent()) {
		my $start = $entry->index('sel.first');
		my $end = $entry->index('sel.last');
		my $sel_text = substr($entry->get(), $start, $end-$start+1);
		my @ids = $sel_text =~ /(\d+)/g;
		foreach (@ids) {
			inspect($_);
		}
	}

}

sub 
copy_selection($) 
{
	my $entry = shift;

	if ($entry->selectionPresent()) {
		my $start = $entry->index('sel.first');
		my $end = $entry->index('sel.last');
		my $sel_text = substr($entry->get(), $start, $end-$start+1);
		print "$sel_text\n";
		$entry->clipboardClear;
		$entry->clipboardAppend($sel_text);
	}

}

sub
inspect($) 
{
	my $id = shift;
	my $thing = undef;
	my @lines;

	if ($id =~ /HASH/) {
		# we've been passed a real thing
		$thing = $id;
	}
	else {
		# we don't have a master list of items, so find it in the tree
		THING: foreach (sort numeric keys %tree) {
			foreach my $tree_thing (@{$tree{$_}}) {
				if ($id == $$tree_thing{id}) {
					$thing = $tree_thing;
					last THING;
				}
			}
		}
	}

	if ($thing) {
		foreach (sort keys %$thing) {
			if (/(walls|cells|pediments|roofs|columns)/) {
				# list of other things
				my $line = "$_ = ($$thing{$_}) [";
				foreach my $child (@{$$thing{$_}}) {
					$line .= " $$child{id}";
				}
				$line .= " ]";
				push @lines, $line;
			}
			elsif (/(room|building|object)/) {
				# other thing
				push @lines, "$_ = ${$$thing{$_}}{id}";
			}
			elsif (/^(rect|heights|filled_res|point_gable_status|change_points)/) {
				# list of scalars
				my $line = "$_ = (";
				foreach my $val (@{$$thing{$_}}) {
					$line .= (defined($val) ? " $val" : ' undef');
				}
				$line .= " )";
				push @lines, $line;
			}
			elsif (/^(resmap|base_points|points|cached_map)/) {
				# list of 2 value lists
				my $line = "$_ = [";
					foreach my $res (@{$$thing{$_}}) {
						$line .= " ($$res[0],$$res[1])";
					}
				$line .= " ]";
				push @lines, $line;
			}
			else {
				# scalar
				push @lines, "$_ = " . (defined($$thing{$_}) ? $$thing{$_} : 'null');
			}
		}
	}
	else {
		push @lines, "No thing found with id $id";
	}

	if (0) {
		print "+" x 80, "\n";
		print "Inspecting $id; gen $gen, $next_id items created\n";
		foreach (@lines) {
			print "$_\n";
		}
		print "+" x 80, "\n\n";
	}
	else {
		my $inspect_win;
		my $inspect_text;
		if (! Exists($inspect_win)) {
			$inspect_win = $main_win->Toplevel();
			$inspect_win->transient($main_win);
			$inspect_win->title("Inspect $id");
			$inspect_win->Button( -text => "Close", -command => sub { $inspect_win->withdraw })->pack(
				$inspect_win->Button( -text => "Dissolve", -command => sub {
					dissolve($thing,$JOIN);
					foreach my $cell (@{$tree{$CELL}}) {
						update_resonances($cell) if $$cell{state} == $SEEK;
					}
					foreach my $wall (@{$tree{$WALL}}) {
						update_resonances($wall) if $$wall{state} & ($BUILD | $COMPLETING);
					}
					$inspect_win->withdraw;
					}), -expand => 1, -fill => 'x');

			$inspect_text = $inspect_win->Scrolled("ROText", -scrollbars => 'osoe',
				-width => 37, -wrap => 'none')->pack(-expand => 1, -fill => 'both');
		}
		else {
			$inspect_win->deiconify();
			$inspect_win->raise();
		}
		my $nbr_buttons = 0;
		my $window_height = $#lines * 22 + 45;
		while ($_ = shift @lines) {
			my ($b,$c,$e);
			# do we look like a label=value pair?
			if (my ($label,$val) = /([^\s]+) = (.+)/) {
				# parse label/value pair

				# create the entry first so the button (if any) can reference it
				if ($val =~ /\[(.*)\]/) {
					$val = $1;
				}
				$e = $inspect_text->Entry(-width => length($val) + 2, -exportselection => 1);
				$e->insert('end', "$val");
				$e->configure(-state => 'readonly');

				# create a label or button
				if ($label =~ /(cells|roofs|pediments|walls|columns|room|building|object)/) {
					$nbr_buttons++;
					$b = $inspect_text->Button(-text => "$label",  -relief => 'groove', -width => 12, -height => 1,
						-command => [ \&inspect_selection, $e ] )
				}
				else {
					$b = $inspect_text->Label(-text => "$label",  -relief => 'groove', -width => 15);
				}

				# $c = $inspect_text->Button(-text => "C",  -relief => 'groove', -width => 2, -height => 1,
					# -command => [ \&copy_selection, $e ] );

				# add label/button, then entry
				# $inspect_text->windowCreate('end', -window => $c);
				$inspect_text->windowCreate('end', -window => $b);
				$inspect_text->windowCreate('end', -window => $e);
				# $inspect_text->insert('end', "$val");
			}
			else {
				$inspect_text->insert('end', "$_");
			}
			$inspect_text->insert('end', "\n") if $#lines > -1;
		}
		$window_height += 6 * $nbr_buttons;
		$inspect_win->geometry("265x$window_height");
	}
}

sub
init_tk() 
{

	$main_win = MainWindow->new;
	foreach (glob("$args{i}/*6x6.png")) {
		print "6x6 glob $_\n" if $debug;
		my ($base,undef,undef) = fileparse($_, '6x6\.png');
		$small_img{$base} = $main_win->Photo(-file => $_);
	}
	foreach (glob("$args{i}/*3d3.png")) {
		my ($base,undef,undef) = fileparse($_, '3d3\.png');
		print "3d3 glob $_, base = $base\n" if $debug;
		$td_img{$base} = $main_win->Photo(-file => $_);
	}

	foreach (glob("$args{r}/*_roof_[01]*.png")) {
		my ($base,undef,undef) = fileparse($_, '\..*');
		$td_img{$base} = $main_win->Photo(-file => "$_");
	}

	$main_win->Button(-text => 'Pause', -command => sub { $stop_flag = !$stop_flag; render_tk_3d(1) if $stop_flag; })->grid(
		$main_win->Button(-text => 'Step', -command => sub { $stop_flag = 2; }),
		$main_win->Button(-text => 'Debug', -command => sub { $debug = !$debug; }),
		$main_win->Button(-text => 'Report', -command => sub { report; }),
		$main_win->Button(-text => 'Inspect', -command => sub { inspect($id_to_inspect); }),
		$main_win->Entry(-textvariable => \$id_to_inspect, -width => 10),
		$main_win->Button(-text => 'Quit', -command => sub { print "Byebye\n"; exit; }),
		-sticky => 'ew');

	$main_win->Button(-text => 'Refresh 2D', -command => sub { render_tk; })->grid(
		$main_win->Button(-text => 'Refresh 3D', -command => sub { render_tk_3d(1); }),
		$main_win->Button(-text => 'Spin', -command => sub { $spin = ($spin + 1) % 4; render_tk_3d(1); }),
		# $main_win->Entry(-textvariable => \$spin, -width => 10),
		$main_win->Button(-text => 'Refresh?', -command => sub { $refresh = !$refresh; }),
		-sticky => 'ew');

	$main_win->Label(-textvariable => \$gen_id_counter, -width => 10)->grid(
		$main_win->Label(-text => 'Stop After'),
		$main_win->Entry(-textvariable => \$stop_after_gen, -width => 10),
		$main_win->Label(-text => 'Debug After'),
		$main_win->Entry(-textvariable => \$debug_after_gen, -width => 10),
		-sticky => 'ew');

	$td_canvas = $main_win->Canvas(
		-background => 'grey',
		-width => $image_x_offset * $GX + $image_x_offset * $GY + 30,
		-height => $image_y_offset * $GX + $image_y_offset * $GY + 100,
		);
	$td_canvas->grid("-","-","-","-","-","-");
	$td_canvas->CanvasBind("<Button-1>", [ \&tracker, Ev('x'), Ev('y') ] );

=for comment
	$td_win = $main_win->Toplevel();
	$td_canvas = $td_win->Canvas(
		-background => 'grey',
		-width => $image_x_offset * $GX + $image_x_offset * $GY + 30,
		-height => $image_y_offset * $GX + $image_y_offset * $GY + 100,
		);
	$td_canvas->pack(-side => 'left');
	$td_win->title('3d view');
	$td_win->geometry("+400+10");
=cut

}

sub
main_loop() 
{

	# pause or step button
	#$main_win->waitVariable(\$stop_flag) if $stop_flag == 1;

	my $report_count = 1000;

	$gen++;

	$gen_id_counter = "$gen / $next_id";

	print "\nGen $gen\n---------\n" if $debug;

	my $start_time = Time::HiRes::time() if $gen % $report_count == 0;

	breed unless $gen % $breed_speed;
	search;

	# delete the dead things
	foreach my $type ($CELL,$WALL,$ROOM,$ROOF,$PEDIMENT) {
		for (my $i=$#{$tree{$type}}; $i >= 0; $i--) {
			my $thing = ${$tree{$type}}[$i];
			splice @{$tree{$type}},$i,1 if $$thing{state} == $DEAD;
		}
	}

	render_tk_3d($stop_flag == 2) if $refresh || $stop_flag == 2;

	# pause at a problem
	$stop_flag = 1 if $gen == $stop_after_gen;
	$debug = 1 if $gen == $debug_after_gen;

	unless ($gen % $report_count) {
		my $end_time = Time::HiRes::time();
		print "\nLoop time = ", $end_time - $start_time;
		report;
	}

	# if we've stepped thru 1 gen, pause
	$stop_flag = 1 if $stop_flag == 2;

}

sub main() 
{

	getopts('di:r:', \%args);

	$debug = $args{d} ? 1 : 0;

	$args{i} ||= "images";
	$args{r} ||= "images/roofs";

	$SIG{INT} = sub { done("Ouch!") };
	
	init_tk;

	if (0) {
		open (LOG_FH, ">>$logfile") or die "Couldn't open $logfile: $!";
		# save stdout
		$stdout_fh = select(LOG_FH);
		# we want unbuffered writing to the log
		$| = 1;
	}

	print "$0 started at ", scalar localtime, "\n";
	print "\$X = $GX, \$Y = $GY\n";

	srand 1;

	if (0) {

		# test object
		my $thing = create({
			type => $RESKEY_THING,
			state => $COMPLETING,
			x => 2,
			y => 2,
			# x_dim => 3,
			# y_dim => 6,
			# resfunc => \&pyramid_res_map,
			# reskey => ...

#			base_points => [ 	
#				[ 3,2 ],
#				[ 6,2 ],
#				[ 6,1 ],
#				[ 12,1 ],
#				[ 12,4 ],
#				[ 14,4 ],
#				[ 14,7 ],
#				[ 11,7 ],
#				[ 11,9 ],
#				[ 9,9 ],
#				[ 9,7 ],
#				[ 6,7 ],
#				[ 6,9 ],
#				[ 3,9 ],
#				],

#			base_points => [ 	
#				[ 0,1 ],
#				[ 1,1 ],
#				[ 1,0 ],
#				[ 2,0 ],
#				[ 2,1 ],
#				[ 3,1 ],
#				[ 3,2 ],
#				[ 2,2 ],
#				[ 2,5 ],
#				[ 4,5 ],
#				[ 4,6 ],
#				[ 1,6 ],
#				[ 1,2 ],
#				[ 0,2 ],
#				],

#			base_points => [ 	
#				[ 0,0 ],
#				[ 4,0 ],
#				[ 4,4 ],
#				[ 6,4 ],
#				[ 6,6 ],
#				[ 0,6 ],
#				],
#
#			# bug in safeloops
#			base_points => [ 	
#				[ 0,0 ],
#				[ 5,0 ],
#				[ 5,15 ],
#				[ 7,15 ],
#				[ 7,17 ],
#				[ 5,17 ],
#				[ 5,19 ],
#				[ 3,19 ],
#				[ 3,17 ],
#				[ 0,17 ],
#				],
#
#			base_points => [ 	
#				[ 0,0 ],
#				[ 3,0 ],
#				[ 3,8 ],
#				[ 0,8 ],
#				],
#
#			# pruning gables
#			base_points => [ 	
#				[ 0,0 ],
#				[ 3,0 ],
#				[ 3,3 ],
#				[ 2,3 ],
#				[ 2,5 ],
#				[ 3,5 ],
#				[ 3,6 ],
#				[ 1,6 ],
#				[ 1,3 ],
#				[ 0,3 ],
#				],

			resfunc => \&single_peak_gable_res_map,
#			resfunc => \&single_peak_res_map,
			no_shared_gables => 1,
			base => 0,
			},$FL_RESONATE) if 1;

	}

	if (0) {

		my @building_rect = ( 2, 2, 20, 18 ) ;
		my $point = [ 
			[ 1,0],
			[ 0,2],
			[ -1,0],
			[ 0,-2],
			];
		my ( $width, $height) = ( 1,1);

		my @grid_sizes = (10,8,6,4,2,0);
		my $grid_size;
		foreach (@grid_sizes) {
			$grid_size = $_;
			# bail out if the smallest grid didn't fit.
			last if $grid_size == 0;
			# fit the plan to our area and convert the unit points to real locations
			print "Checking grid size $grid_size in @building_rect\n";
			last if fit_plan($point, $width, $height, $grid_size, \@building_rect);
		}

		if ($grid_size == 0) {
			print "Couldn't fit plan to area\n";
		}
		else {

			# take the x & y grid sizes off the front of the point list
			my $x_grid = shift @$point;
			my $y_grid = shift @$point;
			print "x_grid, y_grid = $x_grid, $y_grid\n";

			# create the building
			my $building = create_building(
				\@building_rect, $grid_size, $point, $x_grid, $y_grid);
		}
	}

	while (1) {
		main_loop;
		$main_win->update;
		$main_win->waitVariable(\$stop_flag) if $stop_flag == 1;
	}
}

main;

