#!/usr/bin/env perl

use strict;
use warnings;

my $tag_prefix = "AgdaTag";
my $underscore = "AgdaUnderscore";
my $commands   = qr"(InductiveConstructor|CoinductiveConstructor\
                    |Datatype|Field|Function|Module|Postulate|Record)";

while (<>) {

  s|(\\Agda$commands)\{(.*?)\}

   | my $cmd = $1;
     my $arg = $3;
     my $tag = "$tag_prefix-$3" =~ s/\\_/$underscore/gr;

     $_ = "%\n%<*$tag>\n$cmd\{$arg\}%\n%</$tag>\n";
   |gxe;

  print;

}
