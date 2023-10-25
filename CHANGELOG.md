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

* A [change](https://github.com/agda/agda/pull/6639) in 2.6.4 that prevented all recursion on proofs,
  i.e., members of a type `A : Prop ℓ`, has been [reverted](https://github.com/agda/agda/pull/6936).
  It is possible again to use proofs as termination arguments.
  (See [issue #6930](https://github.com/agda/agda/issues/6930).)

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
