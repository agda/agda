{-# OPTIONS --prop #-}

module Issue3526-2 where

open import Agda.Builtin.Equality

record Truth (P : Prop) : Set where
  constructor [_]
  field
    truth : P
open Truth public

data ⊥' : Prop where

⊥ = Truth ⊥'

¬ : Set → Set
¬ A = A → ⊥

unique : {A : Set} (x y : ¬ A) → x ≡ y
unique x y = refl

⊥-elim : (A : Set) → ⊥ → A
⊥-elim A b = {!!}

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

set : Bool → Set
set false = ⊥
set true  = ⊤

set-elim : ∀ b → set b → Set
set-elim b x = {!!}

