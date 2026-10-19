{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical renaming (primTransp to transp; primHComp to hcomp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

-- The with-expression is an hcomp whose base (1) disagrees with its
-- side (constantly 0) on φ = j.  Its type is inferred, and the side
-- condition  u i0 ≡ λ _ → 1  on φ  is never checked.
bad : I → Nat
bad j with hcomp {A = Nat} {φ = j} (λ i _ → 0) 1
... | w = w

-- bad i0 = hcomp {φ = i0} _ 1 = 1  and  bad i1 = (λ i _ → 0) i1 1=1 = 0.
path : 1 ≡ 0
path j = bad j

data ⊥ : Set where

D : Nat → Set
D zero    = ⊥
D (suc _) = Nat

boom : ⊥
boom = transp (λ i → D (path i)) i0 0
