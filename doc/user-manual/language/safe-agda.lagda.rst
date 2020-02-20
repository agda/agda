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

* :option:`--allow-unsolved-metas`; forces Agda to accept unfinished
  proofs.

* :option:`--allow-incomplete-matches`; forces Agda to accept
  unfinished proofs.

* :option:`--no-positivity-check`; makes it possible to write
  non-terminating programs by structural "induction" on non strictly
  positive datatypes.

* :option:`--no-termination-check`; gives loopy programs any type.

* :option:`--type-in-type` and :option:`--omega-in-omega`; allow the
  user to encode the Girard-Hurken paradox.

* :option:`--injective-type-constructors`; together with excluded
  middle leads to an inconsistency via Chung-Kil Hur's construction.

* :option:`--guardedness` together with :option:`--sized-types`;
  currently can be used to define a type which is both inductive and
  coinductive, which leads to an inconsistency. This might be fixed in
  the future.

* :option:`--experimental-irrelevance` and
  :option:`--irrelevant-projections`; enables potentially unsound
  irrelevance features (irrelevant levels, irrelevant data matching,
  and projection of irrelevant record fields, respectively).

* :option:`--rewriting`; turns any equation into one that holds
  definitionally.  It can at the very least break convergence.

* :option:`--cubical` together with :option:`--with-K`; the univalence
  axiom is provable using cubical constructions, which falsifies the K
  axiom.

* The ``primEraseEquality`` primitive together with
  :option:`--without-K`; using ``primEraseEquality``, one can derive
  the K axiom.

The option ``--safe`` is coinfective (see
:ref:`consistency-checking-options`); if a module is declared safe,
then all its imported modules must also be declared safe.

.. NOTE::

   The :option:`--guardedness` and :option:`--sized-types` options are
   both on by default.  However, unless they have been set explicitly
   by the user, setting the ``--safe`` option will turn them both
   off. That is to say that

   .. code-block:: agda

     {-# OPTIONS --safe #-}

   will correspond to ``--safe``, :option:`--no-guardedness`, and
   :option:`--no-sized-types`.  When both

   .. code-block:: agda

     {-# OPTIONS --safe --guardedness #-}

   and

   .. code-block:: agda

     {-# OPTIONS --guardedness --safe #-}

   will turn on ``--safe``, :option:`--guardedness`, and
   :option:`--no-sized-types`.


   Setting both :option:`--sized-types` and :option:`--guardedness`
   whilst demanding that the module is ``--safe`` will lead to an
   error as combining these options currently is inconsistent.
