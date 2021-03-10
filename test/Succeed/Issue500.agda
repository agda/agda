open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_ _++_

_++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

T : ∀ {A n} → Vec A n → Set
T [] = Nat
T (x ∷ xs) = Vec Nat 0

foo : ∀ {A} m n (xs : Vec A m) (ys : Vec A n) → T (xs ++ ys)
foo m n xs ys with {m + n} | xs ++ ys
... | []     = 0
... | z ∷ zs = []
