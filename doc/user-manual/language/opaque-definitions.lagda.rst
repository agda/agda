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
  clauses, which allow the user to list their choice of names that
  should be locally treated as transparent.

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

Since the definition of ``distlℤ`` is in an ``opaque`` block with an
``unfolding ℤ`` clause, it sees through the opacity of ``ℤ``, and of all
names unfolded by ``ℤ``'s opaque block (see below).

What actually unfolds?
----------------------

When an ``opaque`` block is checked, Agda will compute ahead-of-time the
set of names it is allowed to unfold. This set is per-*block*, not
per-*definition*. An ``unfolding`` clause, if it mentions opaque names,
will cause the unfolding sets associated with those names to be added to
the current block.

The following illustrates the behaviour of these rules:

- Unfolding any name in an opaque block will cause any of the *other*
  names in that block to be unfolded as well. Example::

    module _ where private
      opaque
        x : Nat
        y : Nat

        x = 3
        y = 4

      opaque
        unfolding x

        _ : y ≡ 4
        _ = refl

  Here, even though only ``x`` was asked for, ``y`` is also available
  for unfolding.

- Since the unfolding sets brought in by clauses are associated with the
  block, unfolding is transitive::

    module _ where private
      opaque
        x : Nat
        x = 3

      opaque
        unfolding x
        y : Nat
        y = 4 + x

      opaque
        unfolding y
        _ : y ≡ 7
        _ = refl

- Opaque blocks which are lexically nested can also unfold the names of
  their *parent* blocks, even if the name is not in scope when the child
  block is defined::

    module _ where private
      opaque
        x : Nat
        x = 3

        opaque
          y : Nat
          y = 4

          _ : x ≡ 3
          _ = refl

        z : Nat
        z = 5

      opaque
        unfolding y
        _ : z ≡ 5
        _ = refl

  This is because the ``x`` and ``z`` are direct children of the same
  ``opaque`` block: the ``opaque`` block that defines ``y`` does not
  "split" its parent block.

Multiple unfolding clauses are supported, as well as unfolding more than
one name per clause. The syntax for the latter is simply a
space-separated list of names, which must refer to unambiguous
functions::

    module _ where private
      opaque
        x : Nat
        x = 3

      opaque
        y : Nat
        y = 4

      opaque
        z : Nat
        z = 5

      opaque
        unfolding x y
        unfolding z

        _ : x + y + z ≡ 12
        _ = refl

Finally, ``unfolding`` clauses do not introduce new layout context, so
that the following is legal: note that ``y`` appears to the left of
``x``, but is still attached to the same ``unfolding`` clause. This
allows the user their preference for how to lay out their unfolding
sets::

      opaque
        unfolding x
          y
        unfolding z

        _ : x + y + z ≡ 12
        _ = refl

Having an ``unfolding`` clause appear after other definitions, or
outside of ``opaque`` blocks, is a syntax error.

Note that unlike ``abstract`` blocks, which are treated on a per-module
basis, ``opaque`` blocks will only unfold names according to the rules
above::

  module _ where private
    opaque
      x : Nat
      x = 3

    -- opaque
      -- _ : x ≡ 3
      -- _ = refl
      -- Fails with: x != 3 of type Nat

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
