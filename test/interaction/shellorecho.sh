#!/bin/bash

while read line; do
    if [ "${line:0:6}" = "shell " ]; then
        ${line:6}
    else
        echo $line
    fi
done

