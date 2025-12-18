{-# OPTIONS --no-occurrence-analysis #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

F : Bool → Set → Set → Set
F true  _ A = A
F false _ _ = ⊤

_ : {b : Bool} → F b ⊤ ≡ F b Bool
_ = refl
