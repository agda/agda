{-# OPTIONS --no-irrelevant-projections #-}
module ScopeIrrelevantRecordField where

record Bla : Set1 where
  constructor mkBla
  field
    .bla0 bla1 .{bla2 bla3} {bla4 .bla5} : Set

bla0' : Bla -> Set
bla0' = Bla.bla0  -- should fail with bla0 not in scope
