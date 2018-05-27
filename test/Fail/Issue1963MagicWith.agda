-- Andreas, 2016-07-21 adapted from MagicWith.agda
-- Testing correct printing of postfix projections.

{-# OPTIONS --postfix-projections #-}

-- {-# OPTIONS -v tc.cc:60 #-}
-- {-# OPTIONS -v tc.conv.elim:50 #-}

open import Common.Product
open import Common.Nat

record True  : Set where
data   False : Set where

IsZero : Nat → Set
IsZero zero    = True
IsZero (suc _) = False

Uncurry : {A : Set}{B : A → Set} → ((x : A) → B x → Set) → Σ A B → Set
Uncurry F p = F (p .proj₁) (p .proj₂)

F : (n : Nat) → IsZero n → Set
F zero _ = True
F (suc _) ()

-- Trying to match only on p .proj₁ doesn't work since we can't abstract
-- p .proj₁ without also abstracting p .proj₂.
f : (p : Σ Nat IsZero) → Uncurry F p
f p with p .proj₁
f p | zero  = _
f p | suc _ = ?
