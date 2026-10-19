{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

restTy : Bool → Set
restTy true  = Bool → Bool
restTy false = Bool

postulate
  not : Bool → Bool

module M (x : Bool) (@rewrite p : not x ≡ true) where
  test : (y : Bool) → x ≡ y → restTy (not x)
  test .x refl z with true
  test .x refl z | _ = true
