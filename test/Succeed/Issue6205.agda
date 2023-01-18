
open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

record Test (X : Set) : Set₁ where
  field
    Ty : Set

postulate
  A : Set
  F : (S : Test A) → Test.Ty {X = A} S

macro
  myMacro : Term → TC ⊤
  myMacro hole = do
    ty ← withReconstructed true (getType (quote F))
    unify hole ty

test = myMacro
