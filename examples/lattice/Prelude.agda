
module Prelude where

infixr 90 _∘_
infixr 50 _∧_
infix  20 _⟸⇒_
infixl 3  _from_

_from_ : (A : Set) -> A -> A
A from a = a

_∘_ : {A B C : Set} -> (A -> B) -> (C -> A) -> C -> B
(f ∘ g) x = f (g x)

record _∧_ (A B : Set) : Set where
  field
    p₁ : A
    p₂ : B

open _∧_ public renaming (p₁ to fst; p₂ to snd)

_,_ : {A B : Set} -> A -> B -> A ∧ B
x , y = record { p₁ = x; p₂ = y }

swap : {A B : Set} -> A ∧ B -> B ∧ A
swap p = (snd p , fst p)

_⇐⇒_ : Set -> Set -> Set
A ⇐⇒ B = (A -> B) ∧ (B -> A)
