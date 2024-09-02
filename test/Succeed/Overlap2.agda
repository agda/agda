module Overlap2 where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

-- This test case (ported from GHC #20946) checks that overlap is
-- independent of order.

record C123 (A : Set) : Set where
  field c123 : A

open C123 ⦃ ... ⦄

postulate instance
  C123a : C123 (List (List Nat))
  C123b : ∀ {A} → C123 (List (List A))
  C123c : ∀ {A} → C123 (List A)

module M where
  -- Andreas, 2024-06-22
  -- This following pragma is ignored with a warning
  -- because it is not in the same module as the instances.
  {-# OVERLAPS C123b #-}

{-# OVERLAPS C123b #-}

test123 : List (List Nat)
test123 = c123

record C132 (A : Set) : Set where
  field c132 : A

open C132 ⦃ ... ⦄

postulate instance
  C132a : C132 (List (List Nat))
  C132c : ∀ {A} → C132 (List A)
  C132b : ∀ {A} → C132 (List (List A))

{-# OVERLAPS C132b #-}

test132 : List (List Nat)
test132 = c132

record C213 (A : Set) : Set where
  field c213 : A

open C213 ⦃ ... ⦄

postulate instance
  C213b : ∀ {A} → C213 (List (List A))
  C213a : C213 (List (List Nat))
  C213c : ∀ {A} → C213 (List A)

{-# OVERLAPS C213b #-}

test213 : List (List Nat)
test213 = c213

record C321 (A : Set) : Set where
  field c321 : A

open C321 ⦃ ... ⦄

postulate instance
  C321c : ∀ {A} → C321 (List A)
  C321b : ∀ {A} → C321 (List (List A))
  C321a : C321 (List (List Nat))

{-# OVERLAPS C321b #-}

test321 : List (List Nat)
test321 = c321
