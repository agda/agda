..
  ::
  {-# OPTIONS --rewriting --sized-types #-}
  module language.opaque-definitions where

  open import language.built-ins

.. _opaque-definitions:

******************
Opaque definitions
******************

Opaque definitions are a mechanism for controlling unfolding of Agda
definitions, to help with both goal readability and performance. Like
:ref:`abstract definitions <abstract-definitions>`, opaque definitions
will not unfold in general, but *unlike* ``abstract`` definitions,
opacity can be selectively controlled at use-sites.

Our implementation of unfolding control is based on the theory
introduced by Gratzer et. al. in :ref:`Controlling unfolding in type
theory <controlling-unfolding>`, but handled entirely at the elaborator
level, without a dependency on our (cubical) extension types.

Overview
--------

* Functions (and primitive functions) can be marked ``opaque``.
  Outside of ``opaque`` blocks, these behave like postulates.

* Opaque blocks, even in unrelated modules, can have ``unfolding``
  clauses, marking some subset of the opaque names in scope as
  transparent again.

* Opaque definitions do not reduce in type signatures, even inside
  opaque blocks where they would otherwise be unfolded.


Unfolding opaque definitions
----------------------------

Consider an implementation of the integers as an abstract setoid: The
underlying representation is given by pairs of natural numbers,
representing a difference, but day-to-day, we would like to treat ``ℤ``
as its own type.

Our core module might define these operations::

  module Integer where
    opaque
      ℤ : Set
      ℤ = Nat × Nat

      _≡ℤ_ : (x y : ℤ) → Set
      (p , n) ≡ℤ (p' , n') = (p + n') ≡ (p' + n)

      infix 10 _≡ℤ_

      0ℤ : ℤ
      0ℤ = 0 , 0

      1ℤ : ℤ
      1ℤ = 1 , 0

      _+ℤ_ : (x y : ℤ) → ℤ
      (p , n) +ℤ (p' , n') = (p + p') , (n + n')

      _*ℤ_ : (x y : ℤ) → ℤ
      (a , b) *ℤ (c , d) = ((a * c) + (b * d)) , ((a * d) + (b * c))

      infixl 20 _+ℤ_
      infixl 30 _*ℤ_

      -ℤ_ : ℤ → ℤ
      -ℤ (p , n) = (n , p)

We'd now like to prove that the integers form a ring, under the ``_≡ℤ_``
notion of equality. Some of the equations on natural numbers involved
are pretty nasty, though, so this would be very hard to do without a
solver for semiring equations. However, such a solver would also depend
on :ref:`reflection machinery <reflection>`, bloating the dependency
tree of the ``Integer`` module for people who do not care about it
provably forming a ring.

Fortunately, since ``ℤ`` is *opaque* rather than *abstract*, a different
module, say ``Integer-ring``, can provide its own proofs, in an
``opaque`` block that unfolds the definition of ``ℤ``::

  module Integer-ring where
    open Integer

    opaque
      unfolding ℤ

      distlℤ : ∀ x y z → x *ℤ (y +ℤ z) ≡ℤ x *ℤ y +ℤ x *ℤ z
      distlℤ (a , b) (c , d) (e , f) = use-nat-solver where postulate
        use-nat-solver
          : a * (c + e) + b * (d + f) + (a * d + b * c + (a * f + b * e))
          ≡ a * c + b * d + (a * e + b * f) + (a * (d + f) + b * (c + e))

Since the definition of ``distlℤ`` is in an ``opaque unfolding (ℤ)``
block, it sees through the opacity of ``ℤ``, and of every other name
depending on the same abstract block.

Transitive unfolding
--------------------

For every name ``X`` mentioned in the ``unfolding`` clause associated
with an ``opaque`` block, each opaque name that ``X`` (transitively)
unfolds will also be marked transparent. This is necessary to preserve
subject reduction. Consider the following example::

  opaque
    foo : Set
    foo = Nat

  opaque
    unfolding foo

    bar : foo
    bar = 123

If we could unfold ``bar`` independently of ``foo``, we'd end up with
``bar : foo`` reducing to ``123 : Nat``, while in this block, ``foo !=
Nat``. One can observe the transitivity of ``unfolding`` clauses with an
example like this::

  opaque
    unfolding bar

    _ : foo ≡ Nat
    _ = refl

Unfolding in types
------------------

Note that unfolding clauses do not apply to the *type signatures* inside
an ``opaque`` block. Much like for ``abstract`` blocks, this prevents
leakage of implementation details, but it is also necessary to ensure
that the types of names defined by the opaque block remain valid outside
the opaque block. Consider::

  opaque
    S : Set₁
    S = Set

    foo′ : S
    foo′ = Nat

  opaque
    unfolding foo′

    -- bar′ : foo′
    -- bar′ = 123
    -- Error: S should be a sort, but it isn't

If the definition of ``bar′`` were allowed, we would have ``bar′ :
foo′`` in the context. Outside of the relevant opaque blocks, ``foo′``
is not a type, for ``foo′ : S``, and ``S`` is not a sort. In cases like
this, using an auxiliary definition whose type *is* a sort is required::

    -- Lift foo′ to a definition:
    ty′ : Set
    ty′ = foo′

    bar′ : ty′
    bar′ = 123

Since ``ty′ : Set`` is manifestly a well-formed type, even outside of
this opaque block, there is no problem in adding ``bar′ : ty′`` to the
context.

Bibliography
------------

.. _`controlling-unfolding`:

  Daniel Gratzer, Jonathan Sterling, Carlo Angiuli, Thierry Coquand, and
  Lars Birkedal; `“Controlling unfolding in type theory”
  <https://arxiv.org/abs/2210.05420>`_.
