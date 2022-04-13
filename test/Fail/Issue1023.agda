-- Andreas, 2014-01-10
-- Code by Jesper Cockx and Conor McBride and folks from the Coq-club

{-# OPTIONS --cubical-compatible #-}

-- An empty type.

data Zero : Set where

-- A unit type as W-type.

mutual
  data WOne : Set where wrap : FOne -> WOne
  FOne = Zero -> WOne

-- Type equality.

data _<->_ (X : Set) : Set -> Set₁ where
  Refl : X <-> X

-- This postulate is compatible with univalence:

postulate
  iso : WOne <-> FOne

-- But accepting that is incompatible with univalence:

noo : (X : Set) -> (WOne <-> X) -> X -> Zero
noo .WOne Refl (wrap f) = noo FOne iso f

-- Matching against Refl silently applies the conversion
-- FOne -> WOne to f.  But this conversion corresponds
-- to an application of wrap.  Thus, f, which is really
-- (wrap f), should not be considered a subterm of (wrap f)
-- by the termination checker.
-- At least, if we want to be compatible with univalence.

absurd : Zero
absurd = noo FOne iso (\ ())

-- noo should fail termination check.
