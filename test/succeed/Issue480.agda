-- {-# OPTIONS -v tc.polarity:10 #-}
-- Andreas, 2012-09-07 removed phantom types
module Issue480 where

module Simple where

  data Q : Set where
    a : Q

  f : _ → Q
  f a = a

  postulate helper : ∀ {T : Set} → (T → T) → Q

  test₁ : Q → Q
  test₁ = λ { a → a }

  test₂ : Q
  test₂ = helper test₁

  -- Same as test₂ and test₁, but stuck together.
  test₃ : Q
  test₃ = helper λ { a → a } -- this says "Type mismatch when checking that the pattern a has type _45"

module Example where

  infixr 5 _∷_

  data ℕ : Set where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  data List : Set₁ where
    []   : List
    _∷_  : Set → List → List

  data Tree : List → Set₁ where
    tip  : Tree []
    node : ∀ {T Ts} → (cs : T → Tree Ts) → Tree (T ∷ Ts)


  data Q : (n : ℕ) → Set where
    a : {n : ℕ} → Q n
    b : {n : ℕ} → Q n

  test₁ : Q zero → Tree (Q zero ∷ [])
  test₁ = λ
    { a → node λ { a → tip ; b → tip }
    ; b → node λ { a → tip ; b → tip }
    }

  test₂ = node test₁

  test₃ : Tree (Q zero ∷ Q zero ∷ [])
  test₃ = node λ
    { a → node λ { a → tip ; b → tip }
    ; b → node λ { a → tip ; b → tip }
    }
