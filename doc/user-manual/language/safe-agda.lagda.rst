..
  ::
  module language.safe-agda where

.. _safe-agda:

*********
Safe Agda
*********

By using the option :option:`--safe` (as a pragma option, or on the
command-line), a user can specify that Agda should ensure that
features leading to possible inconsistencies should be disabled.

Here is a list of the features :option:`--safe` is incompatible with:

* ``postulate``; can be used to assume any axiom.

* :option:`--allow-unsolved-metas`; forces Agda to accept unfinished
  proofs.

* :option:`--allow-incomplete-matches`
  and pragma :ref:`NON_COVERING <non_covering-pragma>`;
  allows to prove false using a partial function
  or through a partial proof.

* :option:`--no-positivity-check`
  and pragmas :ref:`NO_POSITIVITY_CHECK <no_positivity_check-pragma>`
  and :ref:`POLARITY <polarity-pragma>`;
  make it possible to write non-terminating programs via datatypes
  that are not strictly positive.

* :option:`--no-termination-check`
  and pragmas :ref:`TERMINATING <terminating-pragma>`
  and :ref:`NON_TERMINATING <non_terminating-pragma>`;
  give loopy programs any type.

* :option:`--type-in-type` and :option:`--omega-in-omega`
  and pragma :ref:`NO_UNIVERSE_CHECK <no_universe_check-pragma>`;
  allow the user to encode the Girard-Hurken paradox.

* pragma :ref:`INJECTIVE <injective-pragma>`;
  allows to prove false by declaring a non-injective function as injective.

* pragma :ref:`ETA <eta-pragma>`;
  can be used force eta-equality for unguarded recursive records
  which can make Agda loop.

* :option:`--injective-type-constructors`; together with excluded
  middle leads to an inconsistency via Chung-Kil Hur's construction.

* :option:`--sized-types`; lacks some checks that rule out improper,
  inconsistent uses of sizes.

* :option:`--experimental-irrelevance` and
  :option:`--irrelevant-projections`; enables potentially unsound
  irrelevance features (irrelevant levels, irrelevant data matching,
  and projection of irrelevant record fields, respectively).

* :option:`--rewriting`; turns any equation into one that holds
  definitionally.  It can at the very least break convergence.

* :option:`--cubical=compatible` together with :option:`--with-K`;
  the univalence axiom is provable using cubical constructions,
  which falsifies the K axiom.

* :option:`--without-K` together with :option:`--flat-split`

* The ``primEraseEquality`` primitive together with
  :option:`--without-K`; using ``primEraseEquality``, one can derive
  the K axiom.

* :option:`--allow-exec`; allows system calls during type checking.

* :option:`--no-load-primitives`; allows the user to bind the sort
  and level primitives manually.

* :option:`--cumulativity`; due to its poor heuristic for solving universe
  levels.

* :option:`--large-indices` together with :option:`--without-K` or
  :option:`--forced-argument-recursion`; both of these combinations are known to
  be inconsistent.

* pragma :ref:`COMPILE <foreign-function-interface>`;
  allows to change the meaning of code during compilation.

The option :option:`--safe` is coinfective (see
:ref:`consistency-checking-options`); if a module is declared safe,
then all its imported modules must also be declared safe.
