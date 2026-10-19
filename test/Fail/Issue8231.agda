{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite

data T : ..Nat → Set where
  a : T 0
  b c : T 1

f : ∀ ..n → T n → T n
f 0 a = a
f 1 b = c
f 1 c = b

eq : ∀ x → f 0 x ≡ x
eq a = refl

{-# REWRITE eq #-}

bad : ∀ x → f 1 x ≡ x
bad _ = refl

fail : {A : Set} → A
fail with () <- bad b
