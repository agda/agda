{-# OPTIONS --cubical #-}
module Issue7139 where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Primitive.Cubical renaming
  ( primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp
  ; primHComp to hcomp ; primTransp to transp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

module M (V : Type) (s : V → V) where
  data Loops : V → Type where
    pt : (x : V) → Loops (s x)

  data Point : {x : V} → Loops x → Type where
    isPt : (x : V) → Point (pt x)

  unPt : ∀ {x : V} {y : Loops x} → Point y → V
  unPt (isPt x) = x

open M Nat suc

-- The transpX clause for unPt used to be generated incorrectly, which
-- led to a loss of canonicity.
compute : unPt (transp (λ i → Point (pt 0)) i0 (isPt 0)) ≡ 0
compute _ = 0
