-- Andreas, 2024-07-23
-- Trigger warning InvalidDisplayForm

-- Recursive display form.

postulate R : Set

{-# DISPLAY R = R #-}

-- Invalid display form rhss.

postulate
  A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Set

{-# DISPLAY A0  = Set₁               #-}
{-# DISPLAY A1  = Set | Set          #-}
{-# DISPLAY A2  = ?                  #-}
{-# DISPLAY A3  = _                  #-}
{-# DISPLAY A4  = .Set               #-}
{-# DISPLAY A5  = λ x → x            #-}
{-# DISPLAY A6  = λ()                #-}
{-# DISPLAY A7  = λ{ x → x }         #-}
{-# DISPLAY A8  = Set → Set          #-}
{-# DISPLAY A9  = (X : Set) → X      #-}
{-# DISPLAY A10 = let x = Set in Set #-}
{-# DISPLAY A11 = record {}          #-}
{-# DISPLAY A12 = record Set {}      #-}
{-# DISPLAY A13 = quote Set          #-}
{-# DISPLAY A14 = quoteTerm Set      #-}
{-# DISPLAY A15 = unquote Set        #-}

-- Invalid display form lhss.

data D : Set where
  c : D

data E : Set where
  c : E

pattern p = c

postulate
  L0 L1 L2 L3 L4 L5 : D → Set

{-# DISPLAY L0 x@y         = Set #-}
{-# DISPLAY L1 .Set        = Set #-}
{-# DISPLAY L2 ()          = Set #-}
{-# DISPLAY L3 record{}    = Set #-}
{-# DISPLAY L4 (Set = Set) = Set #-}
{-# DISPLAY L5 p           = Set #-}


-- Expected behavior:
--
-- All display forms in this file should trigger warning InvalidDisplayForm
-- and be marked as dead code.

------------------------------------------------------------------------

record R1 : Set1 where field f : Set
record R2 : Set1 where field f : Set

open R1
open R2

postulate r : R1

-- Andreas, 2024-08-15
-- Trigger warning UselessPragma for bad lhss of display forms

{-# DISPLAY 0 = Set #-}
-- DISPLAY pragma left-hand side must have form 'f e1 .. en'

{-# DISPLAY Set1 = Set #-}
-- Invalid pattern Set1

{-# DISPLAY c = Set #-}
-- Ambiguous constructor c: InvalidDisplayForm.D.c | InvalidDisplayForm.E.c

{-# DISPLAY f = Set #-}
-- Ambiguous projection f: InvalidDisplayForm.R1.f | InvalidDisplayForm.R2.f

{-# DISPLAY r | Set = Set #-}
-- DISPLAY pragma left-hand side must have form 'f e1 .. en'

{-# DISPLAY x@y = Set #-}
-- DISPLAY pragma left-hand side must have form 'f e1 .. en'
