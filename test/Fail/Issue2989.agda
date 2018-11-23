-- Andreas, 2018-03-03, issue #2989
-- Internal error, fixable with additional 'reduce'.

-- Jesper, 2018-11-23: Test case no longer works after fix of #3056.
-- I'm leaving the test case in Fail for documentation purposes.


-- {-# OPTIONS --show-implicit --show-irrelevant #-}
-- {-# OPTIONS -v tc.rec:70 -v tc:10 #-}

postulate
  N : Set
  P : N → Set

record Σ (A : Set) (B : A → Set) : Set where
  constructor pair
  field
    fst : A
    snd : B fst

Σ' : (A : Set) → (A → Set) → Set
Σ' = Σ

record R : Set where
  constructor mkR
  field
    .p : Σ' N P

f : R → Set
f x = let mkR (pair k p) = x in N

-- WAS:
-- Internal error in Agda.TypeChecking.Records.getRecordTypeFields
-- Error goes away if Σ' is replaced by Σ
-- or field is made relevant

-- SAME Problem:
-- f x = let record { p = pair k p } = x in N
-- f x = let record { p = record { fst = k ; snd = p }} = x in N
