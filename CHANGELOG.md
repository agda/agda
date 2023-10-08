Release notes for Agda version 2.9.0
====================================

Installation
------------

* Dropped support for GHC 8.8, 8.10, and 9.0.

* Agda supports GHC versions 9.2.8 to 9.12.2.

Pragmas and options
-------------------

Warnings
--------

* `UselessPragma` warning instead of hard error `NeedOptionRewriting` when a
  `REWRITE` or `BUILTIN REWRITE` pragma is encountered but `--rewriting` is off.

* New warning 'InvalidTacticAttribute' for misplaced `@(tactic ...)` attributes.
  This was silently accepted up to Agda 2.8.0 but raises now the new warning:
  ```agda
  postulate
    @(tactic not-in-scope) _ : Set
  ```

Syntax
------

Additions to the Agda syntax.

* Records can now be created using module-like syntax in place of curly braces
  and semicolons.

  ```agda
  p : Pair Nat Nat
  p = record where
    fst = 2
    snd = 3
  ```

  See [#4275](https://github.com/agda/agda/issues/4275) for the proposal.

Language
--------

Changes to type checker and other components defining the Agda language.

Reflection
----------

Changes to the meta-programming facilities.

Library management
------------------


Interaction and emacs mode
--------------------------

Backends
--------

* New option `--ghc-trace` for GHC Backend to instrument code
  such that the Agda name of the function is printed to `stderr`
  whenever a function is entered.

Issues closed
-------------

For 2.9.0, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.9.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

### Issues for closed for milestone 2.9.0

### PRs for closed for milestone 2.9.0
