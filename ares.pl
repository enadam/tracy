#!/usr/bin/perl -w
#
# ares.pl -- resolve quick mode tracy output
#
# This program is used to make `tracy -quick' output human readable
# by translating symbol addresses to their respective names using
# the symtab appended by tracy at the end of the output.
#
# Usage: ares.pl <tracy-output>
#
# Prints the translated result on stdout.
#

use strict;

my $RE_HEX = qr/0x[0-9a-f]+/;
my %addrs;

open(F, '<', shift)
	or die "$!";

# Skip until SYMTAB and fill %addrs with the transformation table.
do { } until <F> =~ /\bSYMTAB:$/;
while (<F>)
{
	$addrs{$1} = $2 if /($RE_HEX) = (.*)/;
}

# Now go back and replace occurrances of known addresses with their names.
seek(F, 0, 0);
while (($_ = <F>) !~ /\bSYMTAB:$/)
{
	s/((?:ENTER|LEAVE)\[\d+\]) \[($RE_HEX)\]/
		defined $addrs{$2} ? "$1 $addrs{$2}" : $&/e;
	print;
}

# End of ares.pl
