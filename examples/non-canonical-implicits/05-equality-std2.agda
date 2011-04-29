{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --verbose tc.rec:15 #-}
-- {-# OPTIONS --verbose tc.records.ifs:15 #-}
-- {-# OPTIONS --verbose tc.constr.findInScope:15 #-}
-- {-# OPTIONS --verbose tc.term.args.ifs:15 #-}

module 05-equality-std2 where

open import Relation.Binary 
open import Data.Bool hiding (_≟_)

open DecSetoid {{...}}

test = isDecEquivalence
test2 = false ≟ false
