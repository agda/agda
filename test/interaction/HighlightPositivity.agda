module HighlightPositivity where

data A : Set where
  inA : (A -> A) -> A

data B : Set
data C : Set

data B where
  inB : (C -> B) -> B

data C where
  inC : B -> C

record D : Set where
  inductive
  field
    outD : D -> D

endo : Set -> Set
endo X = X -> X

data E : Set where
  inE : endo E -> E

data F (X : Set -> Set) : Set where
  inF : X (F X) -> F X

open import Agda.Builtin.Bool

data GU : Set
GT : Bool -> Set

data GU where
  inGU : ∀ b → GT b -> GU

GT false = Bool
GT true = GU -> Bool

open import Agda.Builtin.Equality

data H : Set where
  inH : ∀ f → f ≡ (λ (x : H) → x) -> H -- non-positive occurrence is
                                       -- in the implicit type of f
