{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

variable
  A B   : Set
  n m l : Nat
  x y   : A

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

const-zero : Nat → Nat
const-zero zero    = zero
const-zero (suc _) = zero

const-zero≡ : const-zero n ≡ zero
const-zero≡ {n = zero}  = refl
const-zero≡ {n = suc _} = refl

+0 : n + const-zero m ≡ n
+0 {n = zero}  = const-zero≡
+0 {n = suc n} = ap suc +0

badRw : n + ⟨ const-zero m ⟩ ≡ n
badRw = +0

{-# REWRITE badRw #-}

ohNo : n + 4 ≡ n
ohNo = refl
