Release notes for Agda version 2.9.0
====================================

Installation
------------

* Dropped support for GHC 8.8, 8.10, and 9.0.

* Agda supports GHC versions 9.2.8 to 9.12.2.

Pragmas and options
-------------------

* Consolidated Cubical-related flags to
  | Old                    | New                                               |
  | ---------------------- | ------------------------------------------------- |
  | `--cubical`            | `--cubical`, or `--cubical=full`                  |
  | `--erased-cubical`     | `--erased-cubical`, or `--cubical=erased`         |
  | `--cubical-compatible` | `--cubical-compatible`, or `--cubical=compatible` |
  | -                      | `--cubical=no-glue`                               |

  For compatibility between modules using different variants of Cubical Agda, see
  [the documentation](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#variants).

Warnings
--------

Syntax
------

Additions to the Agda syntax.

Language
--------

Changes to type checker and other components defining the Agda language.

* Added support for [Cubical Agda without Glue Types](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#cubical-agda-without-glue)
  by using the flag `--cubical=no-glue`,
  a variant of Cubical Agda which disables the Glue types.
  For compatibility with modules using `--cubical[=full]` and `--cubical=erased`, see
  [variants](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#variants).


Reflection
----------

Changes to the meta-programming facilities.

Library management
------------------


Interaction and emacs mode
--------------------------

Backends
--------

Issues closed
-------------

For 2.9.0, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.9.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

### Issues for closed for milestone 2.9.0

### PRs for closed for milestone 2.9.0
