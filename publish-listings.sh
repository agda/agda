#!/bin/bash

cd /tmp
git clone git@github.com:agda/agda-stdlib.git
cd agda-stdlib
git checkout gh-pages
git merge master -m "merge master into gh-pages"
make listings

if [ "`git status --porcelain`" != "" ]; then
  changed=`git status --porcelain | cut -c4-`
  git add -- $changed
  git commit -m "[auto] updated html listings"
fi
