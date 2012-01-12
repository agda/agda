module IrrelevantRecordField where
import Common.Irrelevance  

record R (A : Set) : Set where
  constructor inn
  field
     .out : A

proj : {A : Set} -> R A -> A
proj (inn a) = a
-- needs to fail, since a is irrelevant under inn