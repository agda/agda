{-# OPTIONS --sized-types #-}

-- Andreas, 2024-09-27, issue #7514

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Reflection
open import Agda.Builtin.Size

-- Since Agda 2.6.2, suffix-free universes can be quoted,
-- not sure whether this is intended.

_ = quote Prop
_ = quote Propω
_ = quote Set
_ = quote Setω
_ = quote SSet
_ = quote SSetω
_ = quote LevelUniv
_ = quote IUniv
_ = quote SizeUniv
