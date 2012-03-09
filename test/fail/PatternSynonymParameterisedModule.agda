module PatternSynonymParameterisedModule where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

module M (A : Set) where
  pattern sss x = suc (suc (suc x))

open M ℕ

na : ℕ
na = sss 3

