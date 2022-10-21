open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

data D (A : Set) (x : A) : Set where
  c : A → D A x

f : (A : Set) (x : A) → D A x → A
f A _ (c y) = y

macro
  m : Term → TC ⊤
  m hole = withReconstructed do
    qf ← quoteTC (f (D Nat 0))
    qqf ← quoteTC qf
    typeError (termErr qqf ∷ [])

test = m
