-- Andreas, 2016-10-03, re issue #2231
-- Testing whether the musical coinduction works fine in abstract blocks

{-# OPTIONS --guardedness #-}

module AbstractCoinduction where

infix 1000 ♯_

postulate
  ∞_ : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞_ #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

infixr 5 _≺_

abstract

  ------------------------------------------------------------------------
  -- Streams


  data Stream (A : Set) : Set where
    _≺_ : (x : A) (xs : ∞ (Stream A)) -> Stream A

  head : ∀ {A} -> Stream A -> A
  head (x ≺ xs) = x

  tail : ∀ {A} -> Stream A -> Stream A
  tail (x ≺ xs) = ♭ xs

  ------------------------------------------------------------------------
  -- Stream programs

  infix  8 _∞
  infixr 5 _⋎_
  infix  4 ↓_

  mutual

    data Stream′ (A : Set) : Set1 where
      _≺_ : (x : A) (xs : ∞ (StreamProg A)) -> Stream′ A

    data StreamProg (A : Set) : Set1 where
      ↓_  : (xs : Stream′ A) -> StreamProg A
      _∞'  : (x : A) -> StreamProg A
      _⋎'_ : (xs ys : StreamProg A) -> StreamProg A

  _∞ : ∀ {A : Set} (x : A) -> StreamProg A
  _∞ = _∞'

  _⋎_ : ∀ {A : Set} (xs ys : StreamProg A) -> StreamProg A
  _⋎_ = _⋎'_

  head′ : ∀ {A} → Stream′ A → A
  head′ (x ≺ xs) = x

  tail′ : ∀ {A} → Stream′ A → StreamProg A
  tail′ (x ≺ xs) = ♭ xs

  P⇒′ : ∀ {A} -> StreamProg A -> Stream′ A
  P⇒′ (↓ xs)    = xs
  P⇒′ (x ∞')     = x ≺ ♯ (x ∞)
  P⇒′ (xs ⋎' ys) with P⇒′ xs
  P⇒′ (xs ⋎' ys) | xs′ = head′ xs′ ≺ ♯ (ys ⋎ tail′ xs′)

  mutual

    ′⇒ : ∀ {A} -> Stream′ A -> Stream A
    ′⇒ (x ≺ xs) = x ≺ ♯ P⇒ (♭ xs)

    P⇒ : ∀ {A} -> StreamProg A -> Stream A
    P⇒ xs = ′⇒ (P⇒′ xs)

  ------------------------------------------------------------------------
  -- Stream equality

  infix 4 _≡_ _≈_ _≊_

  data _≡_ {a : Set} (x : a) : a -> Set where
    ≡-refl : x ≡ x

  data _≈_ {A} (xs ys : Stream A) : Set where
    _≺_ : (x≡ : head xs ≡ head ys) (xs≈ : ∞ (tail xs ≈ tail ys)) ->
          xs ≈ ys

  _≊_ : ∀ {A} (xs ys : StreamProg A) -> Set
  xs ≊ ys = P⇒ xs ≈ P⇒ ys

  foo : ∀ {A : Set} (x : A) -> x ∞ ⋎ x ∞ ≊ x ∞
  foo x = ≡-refl ≺ ♯ foo x

  -- The first goal has goal type
  --   head (′⇒ (x ≺ x ∞ ⋎ x ∞)) ≡ head (′⇒ (x ≺ x ∞)).
  -- The normal form of the left-hand side is x, and the normal form of
  -- the right-hand side is x (both according to Agda), but ≡-refl is
  -- not accepted by the type checker:
  --   x != head (′⇒ (P⇒′ (x ∞))) of type .A
  --   when checking that the expression ≡-refl has type
  --   (head (P⇒ (x ∞ ⋎ x ∞)) ≡ head (P⇒ (x ∞)))
