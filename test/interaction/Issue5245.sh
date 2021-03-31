#!/usr/bin/env bash

AGDA=${1}

cd Issue5245

cp safe lib-a.agda-lib
cp b/safe b/lib-b.agda-lib
cp c/safe c/lib-c.agda-lib

${AGDA} --interaction --no-default-libraries --library-file=libs <<EOF
IOTCM "LibA.agda" None Indirect (Cmd_load "LibA.agda" ["--ignore-interfaces"])
EOF

cp no-safe lib-a.agda-lib
cp b/no-safe b/lib-b.agda-lib
cp c/no-safe c/lib-c.agda-lib

rm c/_build/*/agda/LibC.agdai

${AGDA} --interaction --no-default-libraries --library-file=libs <<EOF
IOTCM "LibA.agda" None Indirect (Cmd_load "LibA.agda" [])
EOF

rm -r _build b/_build c/_build
rm lib-a.agda-lib b/lib-b.agda-lib c/lib-c.agda-lib
