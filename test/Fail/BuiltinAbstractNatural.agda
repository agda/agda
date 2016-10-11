-- Andreas, 2016-10-11, AIM XXIV
-- We cannot bind NATURAL to an abstract version of Nat.

abstract
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
