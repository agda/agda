-- 2010-10-15 and 2012-03-09
-- {-# OPTIONS -v tc.conv.irr:50 -v tc.decl.ax:10 #-}

module Issue351 where

import Common.Irrelevance

data _==_ {A : Set1}(a : A) : A -> Set where
  refl : a == a

record R : Set1 where
  constructor mkR
  field
    fromR : Set

reflR : (r : R) -> r == (mkR _)
reflR r = refl {a = _}

record IR : Set1 where
  constructor mkIR
  field
    .fromIR : Set

reflIR : (r : IR) -> r == (mkIR _)
reflIR r = refl {a = _}
-- peeking into the irrelevant argument, we can immediately solve for the meta
