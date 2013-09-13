{-# OPTIONS --copatterns #-}
module InstantiatedRecordModuleNoCopattern where

module M (A : Set1) where

open M      -- underapplied open
open M Set  -- fully applied open

record R : Set2 where
  constructor inn
  field
    out : Set1

r : R
r = inn Set

open R r  -- fully applied open

bla = out

-- This is an ill-formed copattern:
-- field of instantiated record module is not a projection!!
wrong : R
out wrong = Set

-- InstantiatedRecordModuleNoCopattern.agda:23,1-16
-- Not a valid projection for a copattern: out
-- when checking that the clause out wrong = Set has type R
