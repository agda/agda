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

* The reflection primitive `getInstances` will now return instance
  candidates ordered by _specificity_, rather than in unspecified order:
  If a candidate `c1 : T` has a type which is a substitution instance of
  that of another candidate `c2 : S`, `c1` will appear earlier in the
  list.

  As a concrete example, if you have instances `F (Nat → Nat)`, `F (Nat
  → a)`, and `F (a → b)`, they will be returned in this order. See
  [issue #6944](https://github.com/agda/agda/issues/6944) for further
  motivation.

Library management
------------------

* Agda now follows the XDG base directory standard on Unix-like systems,
  see [PR #6858](https://github.com/agda/agda/pull/6858).
  This means, it will look for configuration files in `~/.config/agda` rather than `~/.agda`.

  For backward compatibility, if you still have an `~/.agda` directory, it will look there first.

  No change on Windows, it will continue to use `%APPDATA%` (e.g. `C:/Users/USERNAME/AppData/Roaming/agda`).


Interaction and emacs mode
--------------------------

Other issues closed
-------------------

For 2.6.5, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.5+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

NOTE: This section will be filled by output produced with `closed-issues-for-milestone 2.6.5`.
