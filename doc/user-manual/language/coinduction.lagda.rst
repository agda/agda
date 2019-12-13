.. _coinduction:

***********
Coinduction
***********

The corecursive definitions below are accepted if the option
:samp:`--guardedness` is active:

::

  {-# OPTIONS --guardedness #-}

(An alternative approach is to use :ref:`sized-types`.)

..
  ::
  module language.coinduction where

  open import Agda.Builtin.Nat
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Agda.Builtin.List

  module newcoinduction where

.. _copatterns-coinductive-records:

Coinductive Records
----------------------------------

It is possible to define the type of infinite lists (or streams) of
elements of some type ``A`` as follows,

::

    record Stream (A : Set) : Set where
      coinductive
      field
        hd : A
        tl : Stream A

As opposed to inductive record types, we have to introduce the keyword
``coinductive`` before defining the fields that constitute the record.

It is interesting to note that is not necessary to give an explicit
constructor to the record type ``Stream A``.

..
  ::

    open Stream

    record _×_ (A B : Set) : Set where
      inductive
      constructor _,_
      field
        fst : A
        snd : B


We can as well define bisimilarity (equivalence) of a pair of ``Stream A`` as a
coinductive record.

::

    record _≈_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
      coinductive
      field
        hd-≈ : hd xs ≡ hd ys
        tl-≈ : tl xs ≈ tl ys

Using :ref:`copatterns <copatterns>` we can define a pair of functions
on ``Stream`` such that one returns a ``Stream`` with the elements in
the even positions and the other the elements in odd positions.

..
  ::

    open _≈_

::

    even : ∀ {A} → Stream A → Stream A
    hd (even x) = hd x
    tl (even x) = even (tl (tl x))

    odd : ∀ {A} → Stream A → Stream A
    odd x = even (tl x)

    split : ∀ {A} → Stream A → Stream A × Stream A
    split xs = even xs , odd xs

And merge a pair of ``Stream`` by interleaving their elements.

::

    merge : ∀ {A} → Stream A × Stream A → Stream A
    hd (merge (fst , snd)) = hd fst
    tl (merge (fst , snd)) = merge (snd , tl fst)

Finally, we can prove that split is the left inverse of merge.

::

    merge-split-id : ∀ {A} (xs : Stream A) → merge (split xs) ≈ xs
    hd-≈ (merge-split-id _)  = refl
    tl-≈ (merge-split-id xs) = merge-split-id (tl xs)



Old Coinduction
---------------

.. note::
   This is the old way of coinduction support in Agda. You are advised to use
   :ref:`copatterns-coinductive-records` instead.

To use coinduction it is recommended that you import the module Coinduction from the `standard library <https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary>`_. Coinductive types can then be defined by labelling coinductive occurrences using the delay operator ``∞``:

..
  ::

  open import Agda.Builtin.Coinduction

::

  data Coℕ : Set where
     zero : Coℕ
     suc  : ∞ Coℕ → Coℕ

The type ``∞ A`` can be seen as a suspended computation of type ``A``. It comes with delay and force functions:

.. code-block:: agda

  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

Values of coinductive types can be constructed using corecursion, which does not need to terminate, but has to be productive. As an approximation to productivity the termination checker requires that corecursive definitions are guarded by coinductive constructors. As an example the infinite “natural number” can be defined as follows:
::

  inf : Coℕ
  inf = suc (♯ inf)

The check for guarded corecursion is integrated with the check for size-change termination, thus allowing interesting combinations of inductive and coinductive types. We can for instance define the type of stream processors, along with some functions:
::

  -- Infinite streams.

  data Stream (A : Set) : Set where
    _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

  -- A stream processor SP A B consumes elements of A and produces
  -- elements of B. It can only consume a finite number of A’s before
  -- producing a B.

  data SP (A B : Set) : Set where
    get : (f : A → SP A B) → SP A B
    put : (b : B) (sp : ∞ (SP A B)) → SP A B

  -- The function eat is defined by an outer corecursion into Stream B
  -- and an inner recursion on SP A B.

  eat : ∀ {A B} → SP A B → Stream A → Stream B
  eat (get f)    (a ∷ as) = eat (f a) (♭ as)
  eat (put b sp) as       = b ∷ ♯ eat (♭ sp) as

  -- Composition of stream processors.

  _∘_ : ∀ {A B C} → SP B C → SP A B → SP A C
  get f₁    ∘ put x sp₂ = f₁ x ∘ ♭ sp₂
  put x sp₁ ∘ sp₂       = put x (♯ (♭ sp₁ ∘ sp₂))
  sp₁       ∘ get f₂    = get (λ x → sp₁ ∘ f₂ x)

It is also possible to define “coinductive families”. It is recommended not to use the delay constructor (``♯_``) in a constructor’s index expressions. The following definition of equality between coinductive “natural numbers” is discouraged:

::

  data _≈’_ : Coℕ → Coℕ → Set where
    zero : zero ≈’ zero
    suc  : ∀ {m n} → ∞ (m ≈’ n) → suc (♯ m) ≈’ suc (♯ n)

The recommended definition is the following one:
::

  data _≈_ : Coℕ → Coℕ → Set where
    zero : zero ≈ zero
    suc  : ∀ {m n} → ∞ (♭ m ≈ ♭ n) → suc m ≈ suc n

The current implementation of coinductive types comes with some `limitations <http://article.gmane.org/gmane.comp.lang.agda/763/>`_.
