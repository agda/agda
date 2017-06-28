open import Agda.Builtin.Nat

data B {A : Set} : A → Set where
  b : (a : A) → B a

data C {A : Set} : ∀ {a} → B {A} a → Set where
  c : {a : A} → C (b a)

id : ∀ {b} → C b → B 0
id c = {!!}
