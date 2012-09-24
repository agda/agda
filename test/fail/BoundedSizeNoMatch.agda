{-# OPTIONS --sized-types #-}
-- {-# OPTIONS -v term:10 #-}
module BoundedSizeNoMatch where

open import Common.Size
open import Common.Equality

postulate Size< : Size → Set
{-# BUILTIN SIZELT Size< #-}

T : Size → Set
T i = (j : Size< i) → T j
-- this should not termination check, otherwise
-- eta expansion can loop

-- loops : (i j : Size) → T i ≡ T j
-- loops i j = refl



