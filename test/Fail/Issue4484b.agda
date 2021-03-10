
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record NoEta : Set where
  no-eta-equality
  constructor _,_
  field fst : Nat
        snd : Nat

open NoEta

data ⊥ : Set where

soft-fail : (a : NoEta) (x : Nat) → (fst a , x) ≡ a → ⊥
soft-fail a x ()  -- Should be yellow (not sure if empty)

loop : ⊥
loop = soft-fail (0 , 0) 0 refl
