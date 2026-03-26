{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool renaming (true to tt; false to ff)

f3 : (f : Bool → Bool) (b : Bool) → f (f (f b)) ≡ f b
f3 f ff with f ff
f3 f ff | ff = refl
f3 f ff | tt with f tt
f3 f ff | tt | tt = refl
f3 f ff | tt | ff = refl
f3 f tt with f tt
f3 f tt | tt = refl
f3 f tt | ff with f ff
f3 f tt | ff | tt = refl
f3 f tt | ff | ff = refl
