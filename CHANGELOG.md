Release notes for Agda version 2.6.5
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.6.3.

Pragmas and options
-------------------

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
