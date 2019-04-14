-- Andreas, 2015-08-11, issue reported by Martin Stone Davis

-- {-# OPTIONS -v impossible:10 -v interaction.give:20 #-}

open import Data.Nat.Base using (ℕ)
open import Data.AVL.Value
open import Data.AVL using (Tree; empty)
open import Data.Vec using (Vec)
open import Data.String using (String)
open import Relation.Binary using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (setoid; subst)
open import Data.Nat.Properties using (<-strictTotalOrder)

VecString : Value (setoid ℕ) _
VecString = MkValue (Vec String) (subst _)

empty' : Tree <-strictTotalOrder VecString
empty' = empty {!!}

-- ERROR WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Monad/Trace.hs:56

-- Currently Agsy gives nothing, which is also a weird.
-- It does not report "No solutions found".
-- Somehow, some parts of the solution are not in scope, which might
-- give an internal error that is caught, causing Agsy to discard
-- the solution.
