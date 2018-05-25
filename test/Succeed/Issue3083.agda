
module _ where

module M (A : Set) where
  record R : Set where
    postulate
      B : Set

postulate
  A : Set
  r : M.R A

module M' = M A

open import Agda.Builtin.Reflection
open import Agda.Builtin.List

postulate
  any : {A : Set} → A

macro
  m : Term → TC _
  m goal =
    bindTC (inferType goal) λ goal-type →
    bindTC (normalise goal-type) λ goal-type →
    bindTC (inferType goal-type) λ _ →
    unify goal (def (quote any) [])

g : M'.R.B r
g = m
