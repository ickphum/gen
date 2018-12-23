#!/usr/bin/perl -w

# gen.pl
use strict;

my @l_points = (
	[ 3,3 ],
	[ 7,3 ],
	[ 7,7 ],
	[ 12,7 ],
	[ 12,9 ],
	[ 3,9 ],
	);

my @l2points = (
	[ 3,3 ],
	[ 6,3 ],
	[ 6,1 ],
	[ 12,1 ],
	[ 12,7 ],
	[ 3,7 ],
	);

my @cross_points = (
	[ 4,4 ],
	[ 6,4 ],
	[ 6,1 ],
	[ 8,1 ],
	[ 8,4 ],
	[ 10,4 ],
	[ 10,6 ],
	[ 8,6 ],
	[ 8,8 ],
	[ 6,8 ],
	[ 6,6 ],
	[ 4,6 ],
	);

my $NORTH = 0;
my $EAST = 1;
my $SOUTH = 2;
my $WEST = 3;

my $debug = 0;

sub fill_sides(@) {

	my @points = @_;
	my $prev;

	print "fill_sides\n" if $debug;

	my @map;
	foreach (0..20) { push @map, []; }
	my $min_y = 20;
	my $max_y = 0;
	foreach my $point (@points) {

		if ($prev) {
			# from prev to here
			my ($x,$y) = @$prev;
			my ($end_x,$end_y) = @$point;
			print "Start at $x,$y\n" if $debug;
			$map[$x][$y] = 1;
			$min_y = $y if $min_y > $y;
			$max_y = $y if $max_y < $y;
			while (($end_x - $x) || ($end_y - $y)) {
				print "\tpoint at $x,$y\n" if $debug;
				$map[$x][$y] = 1;
				$min_y = $y if $min_y > $y;
				$max_y = $y if $max_y < $y;
				$x++ if $x < $end_x;
				$x-- if $x > $end_x;
				$y++ if $y < $end_y;
				$y-- if $y > $end_y;
			}
		}
		else {
			push @points, $point;
		}

		$prev = $point;
	}

	foreach my $y ($min_y-1..$max_y+1) {
		foreach my $x (0..20) {
			print $map[$x][$y] ? "*" : " ";
		}
		print "\n";
	}

}
sub
get_direction($$) {
	my ($start, $end) = @_;
	my $dir = undef;

	my $delta_x = $$start[0] - $$end[0];
	my $delta_y = $$start[1] - $$end[1];
	print "get_direction dx = $delta_x, dy = $delta_y\n" if $debug;
	if ($delta_x * $delta_y) {
		print "Angled line ?; from $$start[0],$$start[1] to $$end[0],$$end[1], dx = $delta_x, dy = $delta_y\n";
	}
	elsif ($delta_x > 0) { $dir = $WEST; }
	elsif ($delta_x < 0) { $dir = $EAST; }
	elsif ($delta_y > 0) { $dir = $NORTH; }
	elsif ($delta_y < 0) { $dir = $SOUTH; }

	return $dir;
}

sub shrink_points($) {

	my $points = shift;
	my $prev;
	my $prev_new;
	my $dir = $NORTH;
	my @new_points;

	print "shrink_points\n" if $debug;

	# find the initial direction, ie from the last point to the first
	$dir = get_direction($$points[$#$points], $$points[0]);

	foreach my $point (@$points) {
		if ($prev) {
			# from prev to here
			my ($x,$y) = @$prev;

			my $new_dir = get_direction($prev, $point);

			my $point_delta_x = $new_dir == $NORTH || $dir == $NORTH ? 1 : -1;
			my $point_delta_y = $new_dir == $EAST || $dir == $EAST ? 1 : -1;

			print "Shrink point at $x,$y, dir = $dir, new_dir = $new_dir, dx = $point_delta_x, dy = $point_delta_y\n" if $debug;

			$dir = $new_dir;

			push @new_points, [ $x + $point_delta_x, $y + $point_delta_y ];

			$prev_new = [ $x + $point_delta_x, $y + $point_delta_y ];

		}
		else {
			push @$points, $point;
		}

		$prev = $point;
	}

	@$points = (@new_points);

}

sub grow_points($) {

	my $points = shift;
	my $prev;
	my $prev_new;
	my $dir;
	my @new_points;

	print "grow_points\n" if $debug;

	# find the initial direction, ie from the last point to the first
	$dir = get_direction($$points[$#$points], $$points[0]);

	foreach my $point (@$points) {
		if ($prev) {
			# from prev to here
			my ($x,$y) = @$prev;

			my $new_dir = get_direction($prev, $point);

			my $point_delta_x = $new_dir == $NORTH || $dir == $NORTH ? -1 : 1;
			my $point_delta_y = $new_dir == $EAST || $dir == $EAST ? -1 : 1;

			print "Grow point at $x,$y, dir = $dir, new_dir = $new_dir, dx = $point_delta_x, dy = $point_delta_y\n" if $debug;

			$dir = $new_dir;

			push @new_points, [ $x + $point_delta_x, $y + $point_delta_y ];

			$prev_new = [ $x + $point_delta_x, $y + $point_delta_y ];

		}
		else {
			push @$points, $point;
		}

		$prev = $point;
	}

	@$points = (@new_points);

}

sub 
find_next_change(@) {

	my @points = @_;
	my %end;

	print "find_next_change\n" if $debug;

	for (my $p = 0; $p <= $#points; $p++) {
		my @index;
		print "p = $p\n" if $debug;
		foreach my $i (0 .. 3) {
			push @index, ($p + $i) % ($#points+1);
			print "\tindex = $index[$#index]\n" if $debug;
		}

		my @delta_x;
		my @delta_y;
		foreach my $i (1 .. 3) {
			my ($curr_x, $curr_y) = @{$points[$index[$i]]};
			my ($prev_x, $prev_y) = @{$points[$index[$i-1]]};
			push @delta_x, $curr_x - $prev_x;
			push @delta_y, $curr_y - $prev_y;
			print "\tdx = $delta_x[$#delta_x], dy = $delta_y[$#delta_y]\n" if $debug;
		}

		if (($delta_x[0] * $delta_x[2] < 0) ||
			($delta_y[0] * $delta_y[2] < 0))
		{
			my $width = abs($delta_x[1] + $delta_y[1]);
			$end{$width} = [] unless $end{$width};
			push @{$end{$width}}, $p;
			print "End found, width $width\n" if $debug;
		}
	}

	my @return;
	foreach (sort { $a <=> $b } keys %end) {
		print "width = $_\n" if $debug;
		push @return, int($_/2);
		foreach my $p (@{$end{$_}}) {
			print "p = $p\n" if $debug;
			push @return, $p;
		}
		last;
	}

	return @return;
}
		
sub
prune_points($$)
{
	my ($change_points, $points) = @_;
	my @deleted;

	print "prune_points\n" if $debug;

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
			}
		}
		elsif ($delta_x[0] || $delta_y[0]) {
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
			}
		}
		else {
			print "?\n" if $debug;
		}

		last if $#$points == -1;
	}

}

sub 
find_tile_shapes(@) {

	my @points = @_;
	my $debug = 0;
	my %tiles;

	print "find_tile_shapes\n" if $debug;

	my $prev_dir = get_direction($points[$#points], $points[0]);
	my %tile_shapes;

	for (my $p = 0; $p <= $#points; $p++) {
		my $next = ($p + 1) % ($#points+1);
		my $next_dir = get_direction($points[$p], $points[$next]);
		my ($x,$y) = @{$points[$p]};

		if (! defined($next_dir) && ! defined($prev_dir)) {
			# no dimensions at all; must be a single point
			return;
		}
		elsif (! defined($next_dir)) {
			$next_dir = ($prev_dir + 1) % 4;
		}
		elsif (! defined($prev_dir)) {
			$prev_dir = ($next_dir - 1) % 4;
		}

		# get the previous shape for this point; we may have two points on the
		# same xy location eg ridge ends; use a default shape if no prev exists.
		# my $shape = $tile_shapes{"${x}_${y}"} || "XXXXXXXX";
		my $shape = $tile_shapes{"${x}_${y}"} || [ 'X','X','X','X','X','X','X','X' ];

		# set the low corner ends from from the incoming & outgoing direction
		my $in_corner = $prev_dir * 2;
		my $out_corner = ($next_dir * 2 + 2) % 8;

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

				# this creates a new version seeded from the previous scope's version
				my $in_corner = $in_corner;

				$$shape[$in_corner] = 'L';
				while ($in_corner++ != $out_corner) {
					$in_corner %= 8;
					$$shape[$in_corner] = 'L';
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
		# can't be a M.
		push @{$tile_shapes{$loc}}, ${$tile_shapes{$loc}}[0];
		# convert list to string
		$tile_shapes{$loc} = pack ("A" x 9, @{$tile_shapes{$loc}});
		# any Xs next to Ls become Ms
		$tile_shapes{$loc} =~ s/XL/ML/g;
		$tile_shapes{$loc} =~ s/LX/LM/g;
		# any remaining Xs become Hs
		$tile_shapes{$loc} =~ s/X/H/g;
		# drop the last char (duplicate of first for pattern matching)
		substr $tile_shapes{$loc}, 8, 1, ""; 
		print "$loc = $tile_shapes{$loc}\n" if $debug;

		my ($x,$y) = $loc =~ /(\d+)_(\d+)/;

		push @resmap, [ $x, $y, { shape => $tile_shapes{$loc} } ];
	}

	return \@resmap;
}

my @points = (
	[ 3,3 ],
	[ 6,3 ],
	[ 6,2 ],
	[ 12,2 ],
	[ 12,4 ],
	[ 14,4 ],
	[ 14,7 ],
	[ 11,7 ],
	[ 11,9 ],
	[ 9,9 ],
	[ 9,7 ],
	[ 6,7 ],
	[ 6,6 ],
	[ 3,6 ],
	);

my @change_points;
my $safe_loops;
fill_sides(@points);
find_tile_shapes(@points);
grow_points(\@points);
fill_sides(@points);

while ($#points >= 0) {
	@change_points = find_next_change(@points);
	$safe_loops = shift @change_points;
	print "$safe_loops safe loops\n" if $debug;
	while ($safe_loops--) {
		shrink_points(\@points);
		fill_sides(@points);
		find_tile_shapes(@points);
	}
	prune_points(\@change_points, \@points);
}

@points = (1..5);

push @points, @points[0..2];
foreach (@points) {
	print "$_\n";
}
