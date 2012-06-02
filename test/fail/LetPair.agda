module LetPair where

import Common.Level

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

swap : {A B : Set} → A × B → B × A
swap p =
  let (a , b) = p  -- irrefutable let, should be added to the syntax at some point
  in  (b , a)

-- Not a valid let-declaration
-- when scope checking let (a , b) = p in (b , a)
