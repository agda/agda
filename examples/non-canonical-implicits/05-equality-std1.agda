{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}

module 05-equality-std1 where

open import Relation.Binary using (module DecSetoid; module IsDecEquivalenceWithImplicits)
open import Data.Bool using (false; true; decSetoid)
open DecSetoid decSetoid using (isDecEquivalence)

open IsDecEquivalenceWithImplicits using (_≟_)

test = false ≟ true

