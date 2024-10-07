-- Andreas, 2024-10-07, issue #7535
-- This is a version of Issue6060.agda with Propω instead of Prop.

{-# OPTIONS --cubical --prop -WnoUnsupportedIndexedMatch #-}

open import Agda.Primitive
open import Agda.Builtin.Equality

data S : Set where s : S
data P : Propω where p : P

-- The following is rejected for P : Prop
-- so should also be rejected for P : Propω.

g : (x : S) → s ≡ x → P → S
g .s refl y = s
