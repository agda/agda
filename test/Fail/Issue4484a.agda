
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record Eta : Set where
  constructor _,_
  field fst : Nat
        snd : Nat

open Eta

data ⊥ : Set where

hard-fail : (a : Eta) (x : Nat) → (fst a , x) ≡ a → ⊥
hard-fail a x ()  -- Should be error (refl is valid)

loop : ⊥
loop = hard-fail (0 , 0) 0 refl
