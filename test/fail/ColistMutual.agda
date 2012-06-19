{-# OPTIONS --copatterns #-}
module ColistMutual where

mutual

  data CoList (A : Set) : Set where
    []  : CoList A
    _∷_ : (x : A)(xs : ∞CoList A) → CoList A

  record ∞CoList (A : Set) : Set where
    coinductive
    field out : CoList A

open ∞CoList

mutual

  repeat : {A : Set}(a : A) → CoList A
  repeat a = a ∷ ∞repeat a

  ∞repeat : {A : Set}(a : A) → ∞CoList A
  out (∞repeat a) = repeat a

-- example by Thorsten and Nisse, PAR 2010

data Tree : Set where
  node : CoList Tree → Tree

mutual

  bad : Tree
  bad = node (node [] ∷ bads)

  bads : ∞CoList Tree
  out bads = bad ∷ bads
  -- should not termination check

{-
data Bool : Set where
  true false : Bool

mutual

  shape : Tree → Bool
  shape (node []) = false
  shape (node (_ ∷ l)) = shapes (out l)

  shapes : CoList Tree → Bool
  shapes [] = false
  shapes (t ∷ _) = shape t

-- shape/shapes may not termination check
-}
