-- Andreas, 2012-06-05 let for record patterns

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.term.let.pattern:100 #-}
-- {-# OPTIONS -v tc.lhs.top:100 #-}

module LetPair where

import Common.Level
-- open import Common.Equality

data _×_ (A B : Set) : Set where
  _,_ : (fst : A)(snd : B) → A × B

swap : {A B : Set} → A × B → B × A
swap p =
  let (a , b) = p  -- works only for record patterns
  in  (b , a)
