
************
Cumulativity
************

Basics
------

Since version 2.6.1, Agda supports optional cumulativity of universes
under the ``--cumulativity`` flag.

.. code-block:: agda

  {-# OPTIONS --cumulativity #-}

When the ``--cumulativity`` flag is enabled, Agda uses the subtyping
rule ``Set i =< Set j`` whenever ``i =< j``. For example, in addition
to its usual type ``Set``, ``Nat`` also has the type ``Set₁`` and even
``Set i`` for any ``i : Level``.

..
  ::

  module language.cumulativity where

  open import Agda.Primitive
  open import Agda.Builtin.Nat

  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C : Set ℓ
    n : Nat

  data Vec (A : Set ℓ) : Nat → Set ℓ where
    [] : Vec A 0
    _∷_ : A → Vec A n → Vec A (suc n)

.. code-block:: agda

  _ : Set
  _ = Nat

  _ : Set₁
  _ = Nat

  _ : ∀ {i} → Set i
  _ = Nat

With cumulativity is enabled, one can implement lifting to a higher
universe as the identity function.

.. code-block:: agda

  lift : ∀ {a b} → Set a → Set (a ⊔ b)
  lift x = x

Example usage: N-ary functions
------------------------------

In Agda without cumulativity, it is tricky to define a
universe-polymorphic N-ary function type ``A → A → ... → A → B``
because the universe level depends on whether the number of arguments
is zero:

.. code-block:: agda

  module Without-Cumulativity where

    N-ary-level : Level → Level → Nat → Level
    N-ary-level ℓ₁ ℓ₂ zero    = ℓ₂
    N-ary-level ℓ₁ ℓ₂ (suc n) = ℓ₁ ⊔ N-ary-level ℓ₁ ℓ₂ n

    N-ary : ∀ {ℓ₁ ℓ₂} n → Set ℓ₁ → Set ℓ₂ → Set (N-ary-level ℓ₁ ℓ₂ n)
    N-ary zero    A B = B
    N-ary (suc n) A B = A → N-ary n A B

In contrast, in Agda with cumulativity one can always work with the
highest possible universe level. This makes it much easier to define
the type of N-ary functions.

.. code-block:: agda

  module With-Cumulativity where

    N-ary : Nat → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
    N-ary zero    A B = B
    N-ary (suc n) A B = A → N-ary n A B

    curryⁿ : (Vec A n → B) → N-ary n A B
    curryⁿ {n = zero}  f = f []
    curryⁿ {n = suc n} f = λ x → curryⁿ λ xs → f (x ∷ xs)

    _$ⁿ_ : N-ary n A B → (Vec A n → B)
    f $ⁿ []       = f
    f $ⁿ (x ∷ xs) = f x $ⁿ xs

    ∀ⁿ : ∀ {A : Set ℓ₁} n → N-ary n A (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
    ∀ⁿ zero    P = P
    ∀ⁿ (suc n) P = ∀ x → ∀ⁿ n (P x)


Limitations
-----------

Currently cumulativity only enables subtyping between universes, but
not between any other types containing universes. For example, ``List
Set`` is not a subtype of ``List Set₁``. Agda also does not have
cumulativity for any other types containing universe levels, so ``List
{lzero} Nat`` is not a subtype of ``List {lsuc lzero} Nat``. Such
rules might be added in a future version of Agda.

Constraint solving
------------------

When working in Agda with cumulativity, universe level metavariables
are often underconstrained. For example, the expression ``List Nat``
could mean ``List {lzero} Nat``, but also ``List {lsuc lzero} Nat``,
or indeed ``List {i} Nat`` for any ``i : Level``.

Currently Agda uses the following heuristic to instantiate universe
level metavariables. At the end of each type signature, each mutual
block, or declaration that is not part of a mutual block, Agda
instantiates all universe level metavariables that are *unbounded from
above*. A metavariable ``_l : Level`` is unbounded from above if all
unsolved constraints that mention the metavariable are of the form
``aᵢ =< _l : Level``, and ``_l`` does not occur in the type of any
other unsolved metavariables. For each metavariable that satisfies
these conditions, it is instantiated to ``a₁ ⊔ a₂ ⊔ ... ⊔ aₙ`` where
``a₁ =< _l : Level``, ..., ``aₙ =< _l : Level`` are all constraints
that mention `_l`.

The heuristic as described above is considered experimental and is
subject to change in future versions of Agda.
