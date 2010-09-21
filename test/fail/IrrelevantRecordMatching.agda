-- 2010-09-07 Andreas

module IrrelevantRecordMatching where

record Prod (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

wrongElim : {A : Set} -> .(Prod A A) -> A
wrongElim (a , a') = a
-- needs to fail because a is irrelevant