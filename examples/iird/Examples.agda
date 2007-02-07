
module Examples where

open import LF
open import IIRD
open import IIRDr

-- Some helper functions

infixl 50 _+OP_

_+OP_ : {I : Set}{D : I -> Set1}{E : Set1} -> OP I D E -> OP I D E -> OP I D E
γ₀ +OP γ₁ = σ Two (\x -> case₂ x γ₀ γ₁)

-- First something simple.

bool : OPr One (\_ -> One')
bool _ = ι★r +OP ι★r

Bool : Set
Bool = Ur bool ★

false : Bool
false = intror < ★₀ | ★ >

true : Bool
true = intror < ★₁ | ★ >

-- We don't have universe subtyping, and we only setup large elimination rules.
if_then_else_ : {A : Set1} -> Bool -> A -> A -> A
if_then_else_ {A} b x y = Rr bool (\_ _ -> A) (\_ a _ -> case₂ (π₀ a) y x) ★ b

-- Something recursive

nat : OPr One (\_ -> One')
nat _ = ι★r +OP δ One (\_ -> ★) (\_ -> ι★r)

Nat : Set
Nat = Ur nat ★

zero : Nat
zero = intror < ★₀ | ★ >

suc : Nat -> Nat
suc n = intror < ★₁ | < (\_ -> n) | ★ > >

