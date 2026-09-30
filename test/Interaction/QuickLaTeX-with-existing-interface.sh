#!/bin/sh

AGDA=$1
NAME=QuickLaTeX-with-existing-interface
DIR=latex
GENERATE="$AGDA --latex --latex-dir=$DIR -vcompile:0 $NAME.lagda"

rm -rf $DIR
$GENERATE --ignore-interfaces
$GENERATE --only-scope-checking
cat $DIR/$NAME.tex
rm -rf $DIR
