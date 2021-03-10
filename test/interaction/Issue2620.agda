-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.lhs.unify:65 -v tc.irr:50 #-}

open import Agda.Builtin.Nat

data B {A : Set} : A → Set where
  b : (a : A) → B a

data C {A : Set} : ∀ a → B {A} a → Set where
  c : (a : A) → C a (b a)

id : ∀ {A} {a : A} x → C a x → B 0
id x (c y) = {!!}
