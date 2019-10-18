-- 2010-10-05 Andreas

module TerminationRecordPatternLie where

data Empty : Set where

record Unit : Set where

data Bool : Set where
  true false : Bool

T : Bool -> Set
T true = Unit
T false = Empty

-- Thorsten suggests on the Agda list  thread "Coinductive families"
-- to encode lists as records
record List (A : Set) : Set where
  inductive
  constructor list
  field
    isCons : Bool
    head   : T isCons -> A
    tail   : T isCons -> List A

open List public

-- However, we have to be careful to preserve termination
-- in the presence of a lie

postulate
  lie : {b : Bool} -> T b

-- this function is rejected
-- UPDATE: not rejected, non-eta record patterns are not translated away!
f : {A : Set} -> List A -> Empty
f (list b h t) = f (t lie)

-- since its internal representation is
g : {A : Set} -> List A -> Empty
g l = g (tail l lie)

-- however could record constructors still count as structural increase
-- if they cannot be translated away
-- should we accept this?
--   f (list true h t) = f (t _)
