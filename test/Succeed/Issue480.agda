-- Andreas, 2016-02-02 added Ambiguous

module Issue480 where

module Simple where

  data Q : Set where
    a : Q

  f : Q → Q
  f a = a

  postulate helper : ∀ {T : Set} → (T → T) → Q

  test₁ : Q → Q
  test₁ = λ { a → a }

  test₂ : Q
  test₂ = helper test₁

  -- Same as test₂ and test₁, but stuck together.
  test₃ : Q
  test₃ = helper {Q} λ { a → a } -- this says "Type mismatch when checking that the pattern a has type _45"

module Ambiguous where

  data Q : Set where
    a : Q

  data Overlap : Set where
    a : Overlap

  postulate helper : ∀ {T : Set} → (T → T) → T -- result type needs to be propagated

  test₁ : Q → Q
  test₁ = λ { a → a }

  test₃ : Q
  test₃ = helper λ { a → a }

  _$_ : ∀ {T : Set} → (T → T) → T → T
  f $ x = f x

  test : Q
  test = (λ { a → a }) $ a

  test₂ : _
  test₂ = (λ { a → a }) $ Q.a

module Example where

  infixr 5 _∷_

  data ℕ : Set where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  data List : Set₁ where
    []   : List
    _∷_  : Set → List → List

  data Tree (L : Set) : List → Set₁ where
    tip  : Tree L []
    node : ∀ {T Ts} → (cs : T → Tree L Ts) → Tree L (T ∷ Ts)


  data Q (n : ℕ) : Set where
    a : Q n
    b : Q n

  test₁ : Q zero → Tree ℕ (Q zero ∷ [])
  test₁ = λ
    { a → node λ { a → tip ; b → tip }
    ; b → node λ { a → tip ; b → tip }
    }

  test₂ = node test₁

  test₃ : Tree ℕ (Q zero ∷ Q zero ∷ [])
  test₃ = node λ
    { a → node λ { a → tip ; b → tip }
    ; b → node λ { a → tip ; b → tip }
    }
