#!/bin/bash

cd /tmp
git clone git@github.com:agda/agda-stdlib.git
cd agda-stdlib
git checkout gh-pages
git merge master -m "[auto] merge master into gh-pages"
make listings

if [ "`git status --porcelain`" != "" ]; then
  echo "Updates:"
  git status --porcelain
  changed=`git status --porcelain | cut -c4-`
  git add --all -- $changed
  git commit -m "[auto] updated html listings"
  git push
else
  echo "No changes!"
fi

cd ..
rm -rf agda-stdlib
