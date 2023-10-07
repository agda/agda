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

Language
--------

Changes of the type checker etc. that affect the Agda language.

* [**Breaking**]
  Can no longer match on record constructors in _binders_ (`λ`, `let`, parameter telescopes etc.)
  if the respective record does not have eta.
  For example, this is now rejected:
  ```agda
    record Wrap (A : Set) : Set where
      constructor wrap; no-eta-equality; pattern
      field unwrap : A

    module _ {A} (w@(wrap a) : Wrap A) where
  ```
  Reason for this change:
  Such a binding is interpreted here as `a = unwrap w`.
  The user expectation that `w` is definitionally equal to `wrap a` is only met if `Wrap` admits `eta-equality`.

  Pattern matching on left hand sides of function definitions is unaffected by this change.

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
