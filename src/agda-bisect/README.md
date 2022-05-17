agda-bisect: A frontend to `git bisect`
=======================================

`agda-bisect` is a convenient frontend to `git bisect` that helps
tracking down commits that introduce regressions.

Installation
------------

`cabal install`

Usage
-----

Example: find commit that broke successful test `/path/to/Foo.agda`
between release 2.6.1 and current HEAD.
```
cd /tmp
git clone git@github.com:agda/agda
cd agda
cp /path/to/Foo.agda .
# Optional: check that indeed v2.6.1 is good and HEAD is bad.
# agda-bisect --good v2.6.1 --bad HEAD --dry-run-with-commit v2.6.1 Foo.agda
# agda-bisect --good v2.6.1 --bad HEAD --dry-run-with-commit HEAD Foo.agda
agda-bisect --good v2.6.1 --bad HEAD Foo.agda
```

Full documentation see `agda-bisect --help`.

Installing bash-completion for agda-bisect
------------------------------------------

`make linux` or `make macos`, see [Makefile](Makefile).
