open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality

data Vec (A : Set) : ℕ → Set where
  []   :  Vec A zero
  _∷_  :  ∀{n} (x : A) (xs : Vec A n) → Vec A (suc n)

data All₂ {A : Set} {B : Set} (R : A → B → Set) : ∀ {k} → Vec A k → Vec B k → Set where
  []   :  All₂ R [] []
  _∷_  :  ∀ {k x y} {xs : Vec A k} {ys : Vec B k}
          (r : R x y) (rs : All₂ R xs ys) → All₂ R (x ∷ xs) (y ∷ ys)

Det : ∀ {A : Set} {B : Set} (R : A → B → Set) → Set
Det R = ∀{a b c} → R a b → R a c → b ≡ c

detAll₂ : ∀ {A : Set} {B : Set} (R : A → B → Set) (h : Det R) → Det (All₂ R)
detAll₂ R h [] [] = refl
