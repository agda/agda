-- The option --erased-matches=restricted makes it possible to import
-- Agda.Builtin.Erased.Box-cong. This gives access to []-cong, which
-- computes for refl.

{-# OPTIONS --erased-matches=restricted #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Erased.Box-cong
open import Agda.Builtin.Erased.Erased
open import Agda.Builtin.Unit

_ : []-cong refl ≡ refl {x = [ tt ]}
_ = refl
