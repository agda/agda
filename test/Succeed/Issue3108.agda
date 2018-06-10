open import Agda.Builtin.Nat

variable {n} : Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

cons : ∀ {m A} → A → Vec A m → Vec A (suc m)
cons = _∷_

module _ (A : Set) where
  data Vec' : Nat → Set where
    []  : Vec' 0
    _∷_ : A → Vec' n → Vec' (suc n)

cons' : ∀ {m A} → A → Vec' A m → Vec' A (suc m)
cons' = _∷_
