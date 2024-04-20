-- Records with `pattern` do not have eta enabled, pattern matching should succeed
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.RecordPattern where

record SillyStream (A : Set) : Set where
  inductive; pattern; constructor _∷_
  field head : A
  field tail : SillyStream A

foldSS : {A r : Set} → (A → r → r) → SillyStream A → r
foldSS f (head ∷ tail)  = f head (foldSS f tail)
