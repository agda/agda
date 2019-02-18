..
  ::
  module language.safe-agda where

.. _safe-agda:

*********
Safe Agda
*********

By using the option ``--safe`` (as a pragma option, or on the
command-line), a user can specify that Agda should ensure that
features leading to possible inconsistencies should be disabled.

Here is a list of the features ``--safe`` is incompatible with:

* ``postulate``; can be used to assume any axiom.

* ``--allow-unsolved-metas``; forces Agda to accept unfinished proofs.

* ``--no-positivity-check``; makes it possible to write non-terminating
  programs by structural "induction" on non strictly positive datatypes.

* ``--no-termination-check``; gives loopy programs any type.

* ``--type-in-type`` and ``--omega-in-omega``; allow the user to encode
  the Girard-Hurken paradox.

* ``--injective-type-constructors``; together with excluded middle leads
  to an inconsistency via Chung-Kil Hur's construction.

* ``--guardedness`` together with ``--sized-types``; currently can be
  used to define a type which is both inductive and coinductive, which
  leads to an inconsistency. This might be fixed in the future.

* ``--experimental-irrelevance`` and ``--irrelevant-projections``;
  enables potentially unsound irrelevance features (irrelevant levels,
  irrelevant data matching, and projection of irrelevant record
  fields, respectively).

* ``--rewriting``; turns any equation into one that holds definitionally.
  It can at the very least break convergence.

* ``--cubical`` together with ``--with-K``; the univalence axiom is provable using cubical constructions, which falsifies the K axiom.

* The ``primEraseEquality`` primitive together with ``--without-K``; using ``primEraseEquality``, one can derive the K axiom.

The option ``--safe`` is coinfective (see
:ref:`consistency-checking-options`); if a module is declared safe,
then all its imported modules must also be declared safe.

.. NOTE::

   The ``--safe`` option turns off the ``--guardedness`` and
   ``--sized-types`` options that are both on by default. One of them
   (but not both, see above) can be turned on again by giving either
   ``--guardedness`` or ``--sized-types`` *after* the  ``--safe`` option, e.g.

   .. code-block:: agda

     {-# OPTIONS --safe --guardedness #-}

  will turn on ``--safe``, ``--no-sized-types`` (implied by ``--safe``) and
  ``--guardedness``, while

   .. code-block:: agda

     {-# OPTIONS --guardedness --safe #-}

  will turn on ``--safe``, ``--no-sized-types`` (implied by ``--safe``) and
  ``--no-guardedness`` (implied by ``--safe``; the earlier option
  ``--guardedness`` has been overruled by ``--safe``).
