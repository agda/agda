{-# OPTIONS --show-implicit --show-irrelevant #-}
-- {-# OPTIONS -v tc.conv.irr:20 -v tc.constr.findInScope:20 -v tc.meta:20 -v tc.conv.type:50 -v tc.conv.term:30 -v tc.conv.atom:50 -v tc.inj.use:20 #-}
module Issue631 where

import Common.Level  -- for debug messages

data Bool : Set where
  false true : Bool

F : Bool → Set
F true  = Bool
F false = Bool

postulate
  BAD   : ∀ {u} → F u
  Goal  : Set
  score  : .Goal → Set

buggy : Set
buggy = score _ -- {!!}
-- should remain unsolved
