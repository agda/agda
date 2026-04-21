{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality.Rewrite renaming (primRewriteNoMatch to ⟨_⟩)
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

variable
  A B   : Set
  n m l : Nat
  x y   : A

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

nat-id : Nat → Nat
nat-id zero    = zero
nat-id (suc n) = suc (nat-id n)

nat-id≡ : nat-id n ≡ n
nat-id≡ {n = zero}  = refl
nat-id≡ {n = suc n} = ap suc nat-id≡

+0 : nat-id n + 0 ≡ n
+0 {n = zero}  = nat-id≡
+0 {n = suc n} = ap suc +0

badRw : ⟨ nat-id n ⟩ + 0 ≡ n
badRw = +0

{-# REWRITE badRw #-}

fails : nat-id n + 0 ≡ n
fails = refl
