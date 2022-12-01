module FieldMetaName where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

data T : Bool → Set where
  true : T true

f : ∀ {x : Σ Bool λ _ → Bool} → T (x .fst) → ⊤
f _ = tt

-- Goal display should have _x.snd as the meta name; x from the
-- argument, .snd from eta expansion
_ : ⊤
_ = f true
