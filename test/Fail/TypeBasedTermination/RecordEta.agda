-- Constructors in records with eta equality should not be size-decreasing, see #7206
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.RecordEta where

record SillyStream (A : Set) : Set where
  inductive; eta-equality; constructor _∷_
  field head : A
  field tail : SillyStream A

foldSS : {A r : Set} → (A → r → r) → SillyStream A → r
foldSS f (head ∷ tail)  = f head (foldSS f tail)
