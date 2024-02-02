Release notes for Agda version 2.6.5
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.8.1.

Pragmas and options
-------------------

Syntax
------

Additions to the Agda syntax.

Language
--------

Changes to type checker and other components defining the Agda language.

* Left-hand side let: `using x ← e`

  This new construct can be using in left-hand sides together with `with` and
  `rewrite` to give names to subexpressions. It is the left-hand side
  counterpart of a `let`-binding and supports the same limited form of pattern
  matching on eta-expandable record values.

  It can be quite useful when you have a function doing a series of nested
  `with`s that share some expressions. Something like

  ```agda
  fun : A → B
  fun x using z ← e with foo z
  ... | p with bar z
  ...   | q = r
  ```

  Here the expression `e` doesn't have to be repeated in the two `with`-expressions.

  As in a `with`, multiple bindings can be separated by a `|`, and variables to
  the left are in scope in bindings to the right.

Reflection
----------

Changes to the meta-programming facilities.

Library management
------------------

Interaction and emacs mode
--------------------------

* The Auto command has been reimplemented from the ground up. This fixes
  problems where Auto would fail in the presence of language features it didn't
  know about, such as copatterns or anything cubical.

  The reimplementation does not support case splitting (`-c`), disproving
  (`-d`) or refining (`-r`).

Backends
--------

Other issues closed
-------------------

For 2.6.5, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.5+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

NOTE: This section will be filled by output produced with `closed-issues-for-milestone 2.6.5`.
