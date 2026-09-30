module Issue2762-2 where

open import Agda.Builtin.List
open import Agda.Builtin.Equality

pattern [_] x = x ∷ []

singleton : {A : Set} → A → List A
singleton x = x ∷ []

{-# DISPLAY _∷_ x [] = singleton x #-}

_ : ∀ {A} (x : A) → singleton x ≡ [ x ]
_ = {!!}
