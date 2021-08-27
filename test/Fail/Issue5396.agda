{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

{-# BUILTIN REWRITE _≡_ #-}

not : Bool → Bool
not true = false
not false = true

data Unit : Set where
  unit : Unit

postulate
  X : Unit → Set
  X-Nat : X unit ≡ Nat
  X-Bool : (u : Unit) → X u ≡ Bool
{-# REWRITE X-Nat #-}

0' : (u : Unit) → X u
0' unit = 0

{-# REWRITE X-Bool #-}

test : (u : Unit) → not (0' u) ≡ true
test unit = refl
