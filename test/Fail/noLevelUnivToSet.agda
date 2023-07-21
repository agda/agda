{-# OPTIONS --level-universe #-}

open import Agda.Primitive
open import Agda.Builtin.Equality

_ : LevelUniv ≡ Set
_ = refl

-- Error:
--
-- LevelUniv != Set
-- when checking that the expression refl has type LevelUniv ≡ Set
