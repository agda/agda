Release notes for Agda version 2.9.0
====================================

Installation
------------

* Dropped support for GHC 8.8, 8.10, and 9.0.

* Agda supports GHC versions 9.2.8 to 9.12.2.

Pragmas and options
-------------------

* New option `--print-options` to print a simple list of all options.
  This list can e.g. be used to implement bash completion.

* New flag `--no-write-interfaces`

Warnings
--------

* `UselessPragma` warning instead of hard error `NeedOptionRewriting` when a
  `REWRITE` or `BUILTIN REWRITE` pragma is encountered but `--rewriting` is off.

* New warning `DivergentModalityInClause` when modality of a clause diverges
  from that of the function.  Example:
  ```agda
  A : Set₁
  @0 A = Set
  ```

* New warning `InvalidTacticAttribute` for misplaced `@(tactic ...)` attributes.
  This was silently accepted up to Agda 2.8.0 but raises now the new warning:
  ```agda
  postulate
    @(tactic not-in-scope) _ : Set
  ```

Syntax
------

Changes to the Agda syntax.

* Records can now be created using module-like syntax in place of curly braces
  and semicolons.

  ```agda
  p : Pair Nat Nat
  p = record where
    fst = 2
    snd = 3
  ```

  See [#4275](https://github.com/agda/agda/issues/4275) for the proposal.

* Modality annotations in aliases and let-bindings are now supported
  (PR [#7990]()).
  Example:
  ```agda
    split : {A B C : Set} (@0 p : A × B) (k : @0 A → @0 B → C) → C
    split p k = let @0 (x , y) = q in k x y
      where
      @0 q = p
  ```

* Postfix projections cannot be surrounded by parentheses anymore.
  E.g. these postfix projection applications are now illegal in expressions:
  ```agda
    r (.proj)
    r .(proj)
  ```

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

* A normalization level can now also passed to command `Cmd_constraints`
  ("show constraints", `C-c C-=` in Emacs).
  In Emacs, the normalization level is given as usual by `C-u` prefixes.

  This interface change is **breaking** for frontends to `agda --interaction`
  such as the VSCode `agda-mode`, which need updating.

* Fixed an internal error in `Cmd_helper_function` (`C-c C-h` in Emacs)
  (Issue [#8103](https://github.com/agda/agda/issue/8103)).
  Changed the type of `Goal_HelperFunction` which might be **breaking**
  3rd-party interaction frontends.

* `NON_TERMINATING` functions now only reduce in `IgnoreAbstract` mode of
  commands `Cmd_compute(_toplevel)` (`C-u C-c C-n` in Emacs)
  regardless of whether invoked at toplevel or in a hole
  (Issue [#2410](https://github.com/agda/agda/issue/2410)).

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
