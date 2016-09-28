
open import Agda.Builtin.Nat

data S : Set where
  c : S

module _ (A : Set) where
  test : S
  test with c
  ... | q = {!q!}  -- Splitting on q should succeed

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

module _ {A : Set} {n : Nat} (xs : Vec A n) where

  foo : Vec A n → Nat
  foo [] = 0
  foo (x ∷ ys) with x ∷ xs
  ... | zs = {!zs!}
    -- Splitting on zs should succeed here.
    -- Splitting on xs should fail.
