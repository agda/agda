..
  ::

  {-# OPTIONS --irrelevant-projections #-}

  module language.irrelevance where

  open import Agda.Builtin.Nat
  open import Agda.Builtin.Equality

.. _irrelevance:

***********
Irrelevance
***********

Since version 2.2.8 Agda supports irrelevancy annotations. The general rule is that anything prepended by a dot (.) is marked irrelevant, which means that it will only be typechecked but never evaluated.

Motivating example
==================

One intended use case of irrelevance is data structures with embedded proofs, like sorted lists.  ::

  data _≤_ : Nat → Nat → Set where
    zero≤   : {n : Nat} → zero ≤ n
    suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

  postulate
    p₁  : 0 ≤ 1
    p₂  : 0 ≤ 1

  module No-Irrelevance where
    data SList (bound : Nat) : Set where
      []    : SList bound
      scons : (head : Nat)
            → (head ≤ bound)
            → (tail : SList head)
            → SList bound

Usually, when we define datatypes with embedded proofs we are forced to reason about the values of these proofs. For example, suppose we have two lists ``l₁`` and ``l₂`` with the same elements but different proofs: ::

    l₁ : SList 1
    l₁ = scons 0 p₁ []

    l₂ : SList 1
    l₂ = scons 0 p₂ []

Now suppose we want to prove that ``l₁`` and ``l₂`` are equal:

.. code-block:: agda

    l₁≡l₂ : l₁ ≡ l₂
    l₁≡l₂ = refl

It's not so easy! Agda gives us an error:

.. code-block:: text

  p₁ != p₂ of type 0 ≤ 1
  when checking that the expression refl has type l₁ ≡ l₂

We can't show that ``l₁ ≡ l₂`` by ``refl`` when ``p₁`` and ``p₂`` are relevant. Instead, we need to reason about proofs of ``0 ≤ 1``. ::

    postulate
      proof-equality : p₁ ≡ p₂

Now we can prove ``l₁ ≡ l₂`` by rewriting with this equality: ::

    l₁≡l₂ : l₁ ≡ l₂
    l₁≡l₂ rewrite proof-equality = refl

Reasoning about equality of proofs becomes annoying quickly. We would like to avoid this kind of reasoning about proofs here - in this case we only care that a proof of ``head ≤ bound`` exists, i.e. any proof suffices. We can use irrelevance annotations to tell Agda we don't care about the values of the proofs: ::

  data SList (bound : Nat) : Set where
    []    : SList bound
    scons : (head : Nat)
          → .(head ≤ bound)        -- note the dot!
          → (tail : SList head)
          → SList bound

The effect of the irrelevant type in the signature of scons is that scons’s second argument is never inspected after Agda has ensured that it has the right type. The type-checker ignores irrelevant arguments when checking equality, so two lists can be equal even if they contain different proofs: ::

  l₁ : SList 1
  l₁ = scons 0 p₁ []

  l₂ : SList 1
  l₂ = scons 0 p₂ []

  l₁≡l₂ : l₁ ≡ l₂
  l₁≡l₂ = refl



Irrelevant function types
=========================

For starters, consider irrelevant non-dependent function types:

.. code-block:: agda

  f : .A → B

This type implies that ``f`` does not depend computationally on its argument.


What can be done to irrelevant arguments
----------------------------------------

**Example 1.** We can prove that two applications of an unknown irrelevant function to two different arguments are equal. ::

  -- an unknown function that does not use its second argument
  postulate
    f : {A B : Set} -> A -> .B -> A

  -- the second argument is irrelevant for equality
  proofIrr : {A : Set}{x y z : A} -> f x y ≡ f x z
  proofIrr = refl

**Example 2.** We can use irrelevant arguments as arguments to other irrelevant functions. ::

  id : {A B : Set} -> (.A -> B) -> .A -> B
  id g x = g x

**Example 3.** We can match on an irrelevant argument of an empty type with an absurd pattern ``()``. ::

  data ⊥ : Set where

  zero-not-one : .(0 ≡ 1) → ⊥
  zero-not-one ()

What can't be done to irrelevant arguments
------------------------------------------

**Example 1.** You can't use an irrelevant value in a non-irrelevant context.

.. code-block:: agda

  bad-plus : Nat → .Nat → Nat
  bad-plus n m = m + n

.. code-block:: text

  Variable m is declared irrelevant, so it cannot be used here
  when checking that the expression m has type Nat

**Example 2.** You can't declare the function's return type as irrelevant.

.. code-block:: agda

  bad : Nat → .Nat
  bad n = 1

.. code-block:: text

  Invalid dotted expression
  when checking that the expression .Nat has type Set _47

**Example 3.** You can't pattern match on an irrelevant value.

.. code-block:: agda

  badMatching : Nat → .Nat → Nat
  badMatching n zero    = n
  badMatching n (suc m) = n

.. code-block:: text

  Cannot pattern match against irrelevant argument of type Nat
  when checking that the pattern zero has type Nat

**Example 4.** We also can't match on an irrelevant record (see :ref:`record-types`).

.. code-block:: agda

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst

  irrElim : {A : Set} {B : A → Set} → .(Σ A B) → _
  irrElim (a , b) = ?

.. code-block:: text

  Cannot pattern match against irrelevant argument of type Σ A B
  when checking that the pattern a , b has type Σ A B

If this were allowed, `b` would have type `B a` but this type is not
even well-formed because `a` is irrelevant!

Irrelevant declarations
=======================

Postulates and functions can be marked as irrelevant by prefixing the name with a dot when the name is declared. Irrelevant definitions can only be used as arguments of functions of an irrelevant function type ``.A → B``.

Examples: ::

  .irrFunction : Nat → Nat
  irrFunction zero    = zero
  irrFunction (suc n) = suc (suc (irrFunction n))

  postulate
    .assume-false : (A : Set) → A

An important example is the irrelevance axiom ``irrAx``: ::

  postulate
    .irrAx : ∀ {ℓ} {A : Set ℓ} -> .A -> A

This axiom is not provable inside Agda, but it is often very useful when working with irrelevance.

Irrelevant record fields
========================

Record fields (see :ref:`record-types`) can be marked as irrelevant by
prefixing their name with a dot in the definition of the record type.
Projections for irrelevant fields are only created if option
:option:`--irrelevant-projections` is supplied (since Agda > 2.5.4).

**Example 1.** A record type containing pairs of numbers satisfying certain properties. ::

  record InterestingNumbers : Set where
    field
      n      : Nat
      m      : Nat
      .prop1 : n + m ≡ n * m + 2
      .prop2 : suc m ≤ n

**Example 2.** For any type ``A``, we can define a 'squashed' version ``Squash A`` where all elements are equal. ::

  record Squash (A : Set) : Set where
    constructor squash
    field
      .proof : A

  open Squash

  .unsquash : ∀ {A} → Squash A → A
  unsquash x = proof x

**Example 3.** We can define the subset of ``x : A`` satisfying ``P x`` with irrelevant membership certificates. ::

  record Subset (A : Set) (P : A -> Set) : Set where
    constructor _#_
    field
      elem         : A
      .certificate : P elem

  .certificate : {A : Set}{P : A -> Set} -> (x : Subset A P) -> P (Subset.elem x)
  certificate (a # p) = irrAx p

Dependent irrelevant function types
===================================

Just like non-dependent functions, we can also make dependent functions irrelevant. The basic syntax is as in the following examples:

.. code-block:: agda

    f : .(x y : A) → B
    f : .{x y z : A} → B
    f : .(xs {ys zs} : A) → B
    f : ∀ x .y → B
    f : ∀ x .{y} {z} .v → B
    f : .{{x : A}} → B

The declaration

.. code-block:: agda

  f : .(x : A) → B[x]
  f x = t[x]

requires that ``x`` is irrelevant both in ``t[x]`` and in ``B[x]``. This is possible if, for instance, ``B[x] = C x``, with ``C : .A → Set``.

Dependent irrelevance allows us to define the eliminator for the Squash type: ::

  elim-Squash : {A : Set} (P : Squash A → Set)
                (ih : .(a : A) → P (squash a)) →
                (a⁻ : Squash A) → P a⁻
  elim-Squash P ih (squash a) = ih a

Note that this would not type-check with ``(ih : (a : A) → P (squash a))``.


Irrelevant instance arguments
=============================

Contrary to normal instance arguments, irrelevant instance arguments (see :ref:`instance-arguments`) are not required to have a unique solution. ::

  record ⊤ : Set where
    instance constructor tt

  NonZero : Nat → Set
  NonZero zero    = ⊥
  NonZero (suc _) = ⊤

  pred′ : (n : Nat) .{{_ : NonZero n}} → Nat
  pred′ zero {{}}
  pred′ (suc n) = n

  find-nonzero : (n : Nat) {{x y : NonZero n}} → Nat
  find-nonzero n = pred′ n
