find-cycles: analyse cross-module dependency cycles
===================================================

Installation
------------

In this directory, run `cabal install`

Tested with `cabal` version 3.8.1.0 and `ghc` version 9.2.7

Usage
-----

1. Generate `.hie` files for the modules to be analysed
    * e.g. `make type-check-no-deps`
    * e.g. pass `-fwrite-ide-info` to GHC some other way

2. Run `find-cycles`

3. Visualize the generated `.dot` files
