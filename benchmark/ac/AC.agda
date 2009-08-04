{-# OPTIONS --no-termination-check #-}

module AC where

import Nat
import Bool
import List
import Fin
import Logic
import Vec
import EqProof

open Nat hiding (_<_) renaming (_==_ to _=Nat=_)
open Bool
open List hiding (module Eq)
open Fin renaming (_==_ to _=Fin=_)
open Logic
open Vec

infix 20 _○_
infix 10 _≡_

ForAll : {A : Set}(n : Nat) -> (Vec n A -> Set) -> Set
ForAll      zero   F = F ε
ForAll {A} (suc n) F = (x : A) -> ForAll _ \xs -> F (x ∷ xs)

apply : {n : Nat}{A : Set}(F : Vec n A -> Set) -> ForAll n F -> (xs : Vec n A) -> F xs
apply {zero}  F t (vec vnil)         = t
apply {suc n} F f (vec (vcons x xs)) = apply _ (f x) xs

lambda : {n : Nat}{A : Set}(F : Vec n A -> Set) -> ((xs : Vec n A) -> F xs) -> ForAll n F
lambda {zero } F f = f ε
lambda {suc n} F f = \x -> lambda _ (\xs -> f (x ∷ xs))

data Expr (n : Nat) : Set where
  zro : Expr n
  var : Fin n -> Expr n
  _○_ : Expr n -> Expr n -> Expr n

data Theorem (n : Nat) : Set where
  _≡_ : Expr n -> Expr n -> Theorem n

theorem : (n : Nat) -> ({m : Nat} -> ForAll {Expr m} n \_ -> Theorem m) -> Theorem n
theorem n thm = apply _ thm (map var (fzeroToN-1 n))

module Provable where

  NF : Nat -> Set
  NF n = List (Fin n)

  infix 12 _⊕_

  _⊕_ : {n : Nat} -> NF n -> NF n -> NF n
  []      ⊕ ys              = ys
  x :: xs ⊕ []              = x :: xs
  x :: xs ⊕ y :: ys = if   x < y
                      then x :: (xs ⊕ y :: ys)
                      else y :: (x :: xs ⊕ ys)

  normalise : {n : Nat} -> Expr n -> NF n
  normalise  zro    = []
  normalise (var n) = n :: []
  normalise (a ○ b) = normalise a ⊕ normalise b

  infix 30 _↓

  _↓ : {n : Nat} -> NF n -> Expr n
  (i :: is) ↓ = var i ○ is ↓
  []        ↓ = zro

  infix 10 _=Expr=_ _=NF=_

  _=NF=_ : {n : Nat} -> NF n -> NF n -> Bool
  _=NF=_ = ListEq._==_
    where
      module ListEq = List.Eq _=Fin=_

  substNF : {n : Nat}{xs ys : NF n}(P : NF n -> Set) -> IsTrue (xs =NF= ys) -> P xs -> P ys
  substNF = List.Subst.subst _=Fin=_ (subst {_})

  _=Expr=_ : {n : Nat} -> Expr n -> Expr n -> Bool
  a =Expr= b = normalise a =NF= normalise b

  provable : {n : Nat} -> Theorem n -> Bool
  provable (a ≡ b) = a =Expr= b

module Semantics
  {A     : Set}
  (_==_  : A -> A -> Set)
  (_*_   : A -> A -> A)
  (one   : A)
  (refl  : {x : A} -> x == x)
  (sym   : {x y : A} -> x == y -> y == x)
  (trans : {x y z : A} -> x == y -> y == z -> x == z)
  (idL   : {x : A} -> (one * x) == x)
  (idR   : {x : A} -> (x * one) == x)
  (comm  : {x y : A} -> (x * y) == (y * x))
  (assoc : {x y z : A} -> (x * (y * z)) == ((x * y) * z))
  (congL : {x y z : A} -> y == z -> (x * y) == (x * z))
  (congR : {x y z : A} -> x == y -> (x * z) == (y * z))
  where

  open Provable

  module EqP = EqProof _==_ refl trans
  open EqP

  expr[_] : {n : Nat} -> Expr n -> Vec n A -> A
  expr[ zro   ] ρ = one
  expr[ var i ] ρ = ρ ! i
  expr[ a ○ b ] ρ = expr[ a ] ρ * expr[ b ] ρ

  eq[_] : {n : Nat} -> Theorem n -> Vec n A -> Set
  eq[ a ≡ b ] ρ = expr[ a ] ρ == expr[ b ] ρ

  data CantProve (A : Set) : Set where
    no-proof : CantProve A

  Prf : {n : Nat} -> Theorem n -> Bool -> Set
  Prf thm true  = ForAll _ \ρ -> eq[ thm ] ρ
  Prf thm false = CantProve (Prf thm true)

  Proof : {n : Nat} -> Theorem n -> Set
  Proof thm = Prf thm (provable thm)

  lem0 : {n : Nat} -> (xs ys : NF n) -> (ρ : Vec n A) ->
         eq[ xs ↓ ○ ys ↓ ≡ (xs ⊕ ys) ↓ ] ρ
  lem0 []        ys        ρ = idL
  lem0 (x :: xs) []        ρ = idR
  lem0 (x :: xs) (y :: ys) ρ = if' x < y then less else more
    where
      lhs     = (var x ○ xs ↓) ○ (var y ○ ys ↓)
      lbranch = x :: (xs ⊕ y :: ys)
      rbranch = y :: (x :: xs ⊕ ys)

      P = \z -> eq[ lhs ≡ (if z then lbranch else rbranch) ↓ ] ρ

      less : IsTrue (x < y) -> _
      less x<y = BoolEq.subst {true}{x < y} P x<y
                  (spine (lem0 xs (y :: ys) ρ))
        where
          spine : forall {x' xs' y' ys' zs} h -> _
          spine {x'}{xs'}{y'}{ys'}{zs} h =
            eqProof> (x' * xs') * (y' * ys')
                 === x' * (xs' * (y' * ys'))  by  sym assoc
                 === x' * zs              by  congL h

      more : IsFalse (x < y) -> _
      more x>=y = BoolEq.subst {false}{x < y} P x>=y
                    (spine (lem0 (x :: xs) ys ρ))
        where
          spine : forall {x' xs' y' ys' zs} h -> _
          spine {x'}{xs'}{y'}{ys'}{zs} h =
            eqProof> (x' * xs') * (y' * ys')
                 === (y' * ys') * (x' * xs')  by  comm
                 === y' * (ys' * (x' * xs'))  by  sym assoc
                 === y' * ((x' * xs') * ys')  by  congL comm
                 === y' * zs              by  congL h

  lem1 : {n : Nat} -> (e : Expr n) -> (ρ : Vec n A) -> eq[ e ≡ normalise e ↓ ] ρ
  lem1  zro    ρ = refl
  lem1 (var i) ρ = sym idR
  lem1 (a ○ b) ρ = trans step1 (trans step2 step3)
    where
      step1 : eq[ a ○ b ≡ normalise a ↓ ○ b ] ρ
      step1 = congR (lem1 a ρ)

      step2 : eq[ normalise a ↓ ○ b ≡ normalise a ↓ ○ normalise b ↓ ] ρ
      step2 = congL (lem1 b ρ)

      step3 : eq[ normalise a ↓ ○ normalise b ↓ ≡ (normalise a ⊕ normalise b) ↓ ] ρ
      step3 = lem0 (normalise a) (normalise b) ρ

  lem2 : {n : Nat} -> (xs ys : NF n) -> (ρ : Vec n A) -> IsTrue (xs =NF= ys) -> eq[ xs ↓ ≡ ys ↓ ] ρ
  lem2 xs ys ρ eq = substNF {_}{xs}{ys} (\z -> eq[ xs ↓ ≡ z ↓ ] ρ) eq refl

  prove : {n : Nat} -> (thm : Theorem n) -> Proof thm
  prove thm = proof (provable thm) thm (\h -> h)
    where
      proof : {n : Nat}(valid : Bool)(thm : Theorem n) -> (IsTrue valid -> IsTrue (provable thm)) -> Prf thm valid
      proof false  _      _       = no-proof
      proof true  (a ≡ b) isValid = lambda eq[ a ≡ b ] \ρ ->
          trans (step-a ρ) (trans (step-ab ρ) (step-b ρ))
        where
          step-a : forall ρ -> eq[ a ≡ normalise a ↓ ] ρ
          step-a ρ = lem1 a ρ

          step-b : forall ρ -> eq[ normalise b ↓ ≡ b ] ρ
          step-b ρ = sym (lem1 b ρ)

          step-ab : forall ρ -> eq[ normalise a ↓ ≡ normalise b ↓ ] ρ
          step-ab ρ = lem2 (normalise a) (normalise b) ρ (isValid tt)

