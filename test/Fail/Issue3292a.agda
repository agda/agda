
module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module Vars (A : Set) where
  variable
    x : A

-- Was
--   Panic: Unbound name: Issue3121._.x [0,10,12]@8066984681118411118
--   when checking that the expression
--   {A : Set} (let open Vars A) → ;Issue3121.x ≡ ;Issue3121.x has type _2
-- Should be
--   scope error on x
r : {A : Set} (let open Vars A) → x ≡ x
r = refl
