#!/bin/sh

AGDA=$1

$AGDA --interaction --ignore-interfaces <<EOF
IOTCM "Issue2174a.agda" None Indirect (Cmd_load "Issue2174a.agda" [])
IOTCM "Issue2174a.agda" None Indirect (Cmd_give 0 (intervalsToRange (Just (mkAbsolute "$PWD/Issue2174a.agda")) [Interval (Pn () 1 1 1) (Pn () 1 1 1)]) "F ?")
IOTCM "Issue2174a.agda" None Indirect (Cmd_give 0 (intervalsToRange (Just (mkAbsolute "$PWD/Issue2174a.agda")) [Interval (Pn () 1 1 1) (Pn () 1 1 1)]) "F ? ?")
EOF
