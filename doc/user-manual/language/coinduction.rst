.. _coinduction:

***********
Coinduction
***********

.. _copatterns-coinductive-records:

Copatterns and Coinductive Records
----------------------------------

.. note::
   This is a stub.

Old Coinduction
---------------

.. note::
   This is the old way of coinduction support in Agda. You are advised to use
   :ref:`copatterns-coinductive-records` instead.

.. note::
   The type constructor ``∞`` can be used to prove absurdity!

To use coinduction it is recommended that you import the module Coinduction from the `standard library <http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary>`_. Coinductive types can then be defined by labelling coinductive occurrences using the delay operator ``∞``:
::

  data Coℕ : Set where
     zero : Coℕ
     suc  : ∞ Coℕ → Coℕ

The type ``∞ A`` can be seen as a suspended computation of type ``A``. It comes with delay and force functions:
::

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

  data _≈_ : Coℕ → Coℕ → Set where
    zero : zero ≈ zero
    suc  : ∀ {m n} → ∞ (m ≈ n) → suc (♯ m) ≈ suc (♯ n)

The recommended definition is the following one:
::

  data _≈_ : Coℕ → Coℕ → Set where
    zero : zero ≈ zero
    suc  : ∀ {m n} → ∞ (♭ m ≈ ♭ n) → suc m ≈ suc n

The current implementation of coinductive types comes with some `limitations <http://article.gmane.org/gmane.comp.lang.agda/763/>`_.
