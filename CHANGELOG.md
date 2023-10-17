Release notes for Agda version 2.6.5
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.8.1.

* Verbose output printing via `-v` or `--verbose` is now only active if Agda is built with the `debug` cabal flag.
  Without `debug`, no code is generated for verbose printing, which makes building Agda faster and Agda itself
  faster as well.

* Removed the cabal flag `cpphs` that enabled building Agda with `cpphs` instead of the default C preprocessor.

Pragmas and options
-------------------

Syntax
------

Additions to the Agda syntax.

Language
--------

Changes of the type checker etc. that affect the Agda language.

Reflection
----------

Changes to the meta-programming facilities.

Library management
------------------

Interaction and emacs mode
--------------------------

Other issues closed
-------------------

For 2.6.5, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.5+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

NOTE: This section will be filled by output produced with `closed-issues-for-milestone 2.6.5`.
