Release notes for Agda version 2.6.4.1
======================================

This is a minor release of Agda 2.6.4 featuring a few changes:

- Make recursion on proofs legal again.
- Improve performance, e.g. by removing debug printing unless built with cabal flag `debug`.
- Switch to XDG directory convention.
- Reflection: change to order of results returned by `getInstances`.
- Fix some internal errors.

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.8.1.

* Verbose output printing via `-v` or `--verbose` is now only active if Agda is built with the `debug` cabal flag.
  Without `debug`, no code is generated for verbose printing, which makes building Agda faster and Agda itself
  faster as well. (PR [#6863](https://github.com/agda/agda/pull/6863))

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


Other issues closed
-------------------

For 2.6.4.1, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.4.1+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

- [#6746](https://github.com/agda/agda/issues/6746): Support GHC 9.8
- [#6852](https://github.com/agda/agda/issues/6852): Follow XDG Base Directory Specification
- [#6913](https://github.com/agda/agda/issues/6913): Internal error on `primLockUniv`-sorted functions
- [#6930](https://github.com/agda/agda/issues/6930): Termination checking with --prop: change in 2.6.4 compared with 2.6.3
- [#6931](https://github.com/agda/agda/issues/6931): Internal error with an empty parametrized module from a different file
- [#6941](https://github.com/agda/agda/issues/6941): Interaction between opaque and instance arguments
- [#6944](https://github.com/agda/agda/issues/6944): Order instances by specificity for reflection
