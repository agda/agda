{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


test : (x : Nat) → @rew {x ≡ 0} → 0 ≡ x
test x = {!   !}



module _ (x : Nat) (@rew eq : x ≡ 1) where

  foo : (x ≡ 0) → _
  foo refl = {!   !}


module _ (f : Nat → Nat) (@rew eq : f 0 ≡ 1) where

  bar : (f ≡ λ _ → 0) → _
  bar refl = {!   !}
