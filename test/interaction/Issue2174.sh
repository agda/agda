#!/bin/sh

AGDA=$1

$AGDA --interaction --ignore-interfaces <<EOF
IOTCM "Issue2174.agda" None Indirect (Cmd_load "Issue2174.agda" [])
IOTCM "Issue2174.agda" None Indirect (Cmd_infer Instantiated 0 (intervalsToRange (Just (mkAbsolute "$PWD/Issue2174.agda")) [Interval (Pn () 42 5 7) (Pn () 45 5 10)]) "F ?")
IOTCM "Issue2174.agda" NonInteractive Direct (Cmd_give WithoutForce 0 (intervalsToRange (Just (mkAbsolute "$PWD/Issue2174.agda")) [Interval (Pn () 42 5 7) (Pn () 45 5 10)]) "F ?")
EOF
