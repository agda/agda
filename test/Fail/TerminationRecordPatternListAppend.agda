-- 2010-10-06 Andreas

module TerminationRecordPatternListAppend where

data Empty : Set where

record Unit : Set where
  constructor unit

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

-- if the record constructor list was counted as structural increase
-- Thorsten's function would not be rejected
-- UPDATE: and indeed it's not. Safe because we don't translate away
-- non-eta record patterns.
append : {A : Set} -> List A -> List A -> List A
append (list true  h t) l' = list true h (\ _ -> append (t _) l')
append (list false _ _) l' = l'

-- but translating away the record pattern produces something
-- that is in any case rejected by the termination checker
append1 : {A : Set} -> List A -> List A -> List A
append1 {A} l' l = append1' (isCons l') (head l') (tail l') l
  where
    append1' : (isCons : Bool)
               (head   : T isCons -> A)
               (tail   : T isCons -> List A) ->
               List A -> List A
    append1' true  h t l = list true h \ _ -> append1 (t _) l
    append1' false h t l = l
