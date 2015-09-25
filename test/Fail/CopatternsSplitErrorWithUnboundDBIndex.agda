-- Andreas, 2013-10-26
-- What if user tried to eliminate function type by copattern?

{-# OPTIONS --copatterns #-}
-- {-# OPTIONS -v tc.lhs.split:30 #-}

module CopatternsSplitErrorWithUnboundDBIndex where

import Common.Level

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

-- pair defined by copatterns
test : {A B : Set} → A → A → A × A
fst test a = a
snd test a = a

-- Bad error WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Rules/LHS.hs:250

-- Correct error:
-- Cannot eliminate type A → A → A × A with projection pattern fst
-- when checking that the clause fst test a = a has type
-- {A : Set} → {Set} → A → A → A × A
--

-- pair defined by copatterns
pair : {A B : Set} → A → B → A × B
fst pair a b = a
snd pair a b = b

-- Bad error WAS: Unbound index in error message:
--
-- Cannot eliminate type @3 × A with pattern b (did you supply too many arguments?)
-- when checking that the clause fst pair a b = a has type
-- {A B : Set} → A → B → A × B

