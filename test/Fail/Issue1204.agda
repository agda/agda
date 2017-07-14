{-# OPTIONS --warning=error #-}

module _ where

module A where
  postulate
    Nat : Set
    suc : Nat → Nat

open A

syntax suc x = ⟦ x ⟧

-- Error WAS:
-- Names out of scope in fixity declarations: suc

-- Error SHOULD BE something like:
-- Name 'suc' not declared in same scope as its syntax declaration.
