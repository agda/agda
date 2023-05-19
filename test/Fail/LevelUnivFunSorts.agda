{-# OPTIONS --level-universe #-}

open import Agda.Primitive

_ = Set → Level

-- Error:
--
-- funSort Set₁ LevelUniv is not a valid sort
-- when checking that the expression Set → Level is a type
