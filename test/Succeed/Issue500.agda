open import Agda.Builtin.Equality
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

-- Andreas, 2025-04-08, issue #7788
-- Needs also to work with nested with.

postulate
  com : ∀ n m → n + m ≡ m + n

thm : ∀ a b c → a + (b + c) ≡ (c + b) + a
thm a b c with {b + c} | com b c
... | refl with c + b
... | cb with com a cb
... | p rewrite p = refl
