..
  ::
  module language.safe-agda where

.. _safe-agda:

*********
Safe Agda
*********

By using the command-line option ``--safe``, a user can
specify that Agda should ensure that features leading to
possible inconsistencies should be disabled.

Here is a list of the features ``--safe`` is incompatible with:

* ``postulate`` can be used to assume any axiom.

* ``--allow-unsolved-metas`` forces Agda to accept unfinished proofs.

* ``--no-positivity-check`` makes it possible to write non-terminating
  programs by structural "induction" on non strictly positive datatypes.

* ``--no-termination-check`` gives loopy programs any type.

* ``--type-in-type`` allows the user to encode the Girard-Hurken paradox.

* ``--injective-type-constructors`` together with excluded middle leads
  to an inconsistency via Chnug-Kil Hur's construction.

* ``guardedness-preserving-type-constructors`` is based on a rather
  operational understanding of ``∞``/``♯_``; it's not yet clear if
  this extension is consistent.

* ``--experimental-irrelevance`` enables potentially unsound irrelevance
  features (irrelevant levels, irrelevant data matching).

* ``--rewriting`` turns any equation into one that holds definitionally.
  It can at the very least break convergence.


Known Issues
============

Pragma Option
-------------

It is possible to specify ``{-# OPTIONS --safe #-}`` at the top of a file.
Unfortunately a known bug (see `#2487 <https://github.com/agda/agda/issues/2487>`_)
means that the option choice is not repercuted in the imported file. Therefore
only the command-line option can be trusted.

Standard Library
----------------

The standard library uses a lot of unsafe features (e.g. ``postulate`` in
the Foreign Function Interface) and these are not isolated in separate
modules. As a consequence virtually any project relying on the standard
library will not be successfully typechecked with the ``--safe`` option.
There is `work in progress <https://github.com/agda/agda-stdlib/issues/143>`_
to fix this issue.
