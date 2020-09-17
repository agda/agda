#!/bin/sh

AGDA=$1
DIR=$PWD

$AGDA --interaction --ignore-interfaces <<EOF
IOTCM "$DIR/Issue4929.agda" NonInteractive Indirect ( Cmd_load "$DIR/Issue4929.agda" [] )
IOTCM "$DIR/Issue4929.agda" NonInteractive Indirect ( Cmd_give WithoutForce 0 (intervalsToRange (Just (mkAbsolute "$DIR/Issue4929.agda")) [Interval (Pn () 657 24 45) (Pn () 667 24 55)]) "test snt ?" )
EOF
