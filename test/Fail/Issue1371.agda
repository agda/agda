open import Common.Prelude
open import Common.Reflection
open import Common.Equality

` : Term → Term
` (def f []) = con (quote def) (vArg (lit (qname f)) ∷ vArg (con (quote []) []) ∷ [])
` _ = lit (string "other")

macro
  primQNameType : QName → Tactic
  primQNameType f hole =
    bindTC (getType f) λ a →
    bindTC (normalise a) λ a →
    give (` a) hole

A : Set
a : A
A = _

B : Set
b : B
B = _

aName=bName : primQNameType a ≡ primQNameType b
aName=bName = refl

a = 0
b = 1.0

empty : ⊥
empty with aName=bName
... | ()
