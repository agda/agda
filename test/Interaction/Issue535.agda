
module Issue535 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

replicate : ∀ {A n} → A → Vec A n
replicate {n = n} x = {!n!}

replicate′ : ∀ {n A} → A → Vec A n
replicate′ {n} x = {!n!}

extlam : Nat → {n m : Nat} → Vec Nat n
extlam = λ { x {m = m} → {!m!} }
