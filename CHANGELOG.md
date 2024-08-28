Release notes for Agda version 2.8.0
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.10.1.

Pragmas and options
-------------------

* New warning `InvalidDisplayForm` instead of hard error
  when a display form is illegal (and thus ignored).

* New warning `WithClauseProjectionFixityMismatch` instead of hard error
  when in a with-clause a projection is used in a different fixity
  (prefix vs. postfix) than in its parent clause.

* New error warning `TooManyArgumentsToSort` instead of hard error.

* Warning `AbsurdPatternRequiresNoRHS` has been renamed to
  `AbsurdPatternRequiresAbsentRHS`.

Syntax
------

Additions to the Agda syntax.

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

* Emacs: new face `agda2-highlight-cosmetic-problem-face`
  for highlighting the new aspect `CosmeticProblem`.

* Emacs: new face `agda2-highlight-instance-problem-face`
  for highlighting the new aspect `InstanceProblem`.


Backends
--------

Other issues closed
-------------------

For 2.8.0, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.8.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

NOTE: This section will be filled by output produced with `closed-issues-for-milestone 2.8.0`.
