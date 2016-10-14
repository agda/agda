
module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

postulate
  A : Set

module _ (X : Set) where

  macro
    give : Name → Term → TC ⊤
    give x goal = unify (def x []) goal

  B : Set
  B = give A
