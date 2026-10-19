{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

data T : Nat → Prop where
  To : T zero
  Tn : ∀ n → T n

ummm : ∀ n → T n → {!   !}
ummm n t = {! t  !}
