
{-
  A simple stack language example. Illustrating that one
  wants dependent elimination of inductive families.
-}

module StackLanguage where

open import Lib.Nat
open import Lib.Vec
open import Lib.Id

data Prog (A : Set) : Nat -> Set where
  init : Prog A 0
  push : forall {n} -> A -> Prog A n -> Prog A (suc n)
  pop  : forall {n} -> Prog A (suc n) -> Prog A n

⟦_⟧ : forall {A n} -> Prog A n -> Vec A n
⟦ init     ⟧ = ε
⟦ push x p ⟧ = x ► ⟦ p ⟧
⟦ pop p    ⟧ with ⟦ p ⟧
...             | x ► xs = xs

reify : forall {A n} -> Vec A n -> Prog A n
reify ε        = init
reify (x ► xs) = push x (reify xs)

normalise : forall {A n} -> Prog A n -> Prog A n
normalise p = reify ⟦ p ⟧

_≅_ : forall {A n} -> Prog A n -> Prog A n -> Set
p₁ ≅ p₂ = ⟦ p₁ ⟧ == ⟦ p₂ ⟧

sound : forall {A n} -> (p : Prog A n) -> normalise p ≅ p
sound init       = refl
sound (push x p) = cong (_►_ x) (sound p)
sound (pop p)    with ⟦ p ⟧ | sound p
...           | x ► xs | ih with ⟦ reify xs ⟧
sound (pop p) | x ► xs | refl  | .xs = refl
