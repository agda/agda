
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.List

Id : (A : Set) → A → A → Set
Id _ = _≡_

pattern suc² n = suc (suc n)
pattern suc³ n = suc (suc² n)

_ : (n : Nat) → Id Nat (suc³ n) (suc (suc n))
_ = {!!}

data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

pattern [_] x = x ∷ []

foo : List Nat → List Nat
foo [] = {!!}
foo (x ∷ xs) = {!!}

bar : Nat → Nat
bar zero = {!!}
bar (suc zero) = {!!}
bar (suc² n) = {!!}

_ : ∀ x → Id (Vec Nat _) [ x ] [ x ]
_ = {!!}
