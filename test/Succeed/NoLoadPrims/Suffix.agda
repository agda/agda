{-# OPTIONS --no-load-primitives #-}
module NoLoadPrims.Suffix where

open import NoLoadPrims.Base

-- Suffixed names work in modules that import modules that define the
-- primitive sorts
_ : Type₁
_ = Type
