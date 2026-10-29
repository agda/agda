#!/bin/sh

AGDA=$1

$AGDA --interaction --ignore-interfaces --color=never <<EOF2
IOTCM "Issue8858.agda" None Indirect (Cmd_load "Issue8858.agda" [])
IOTCM "Issue8858.agda" NonInteractive Direct (Cmd_give WithoutForce 1 (intervalsToRange (Just (mkAbsolute "$PWD/Issue8858.agda")) [Interval () (Pn () 195 18 11) (Pn () 204 18 20)]) "con x y")
IOTCM "Issue8858.agda" NonInteractive Direct (Cmd_highlight 1 (intervalsToRange (Just (mkAbsolute "$PWD/Issue8858.agda")) [Interval () (Pn () 193 18 9) (Pn () 200 18 16)]) "con x y")
IOTCM "Issue8858.agda" NonInteractive Direct (Cmd_refine_or_intro False 0 (intervalsToRange (Just (mkAbsolute "$PWD/Issue8858.agda")) [Interval () (Pn () 96 9 7) (Pn () 99 9 10)]) "")
IOTCM "Issue8858.agda" NonInteractive Direct (Cmd_highlight 0 (intervalsToRange (Just (mkAbsolute "$PWD/Issue8858.agda")) [Interval () (Pn () 94 9 5) (Pn () 122 9 33)]) "record { foo = ? ; bar = ? }")
EOF2
