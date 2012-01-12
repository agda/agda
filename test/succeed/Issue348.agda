module Issue348 where

import Common.Irrelevance  

data _==_ {A : Set1}(a : A) : A -> Set where
  refl : a == a

record R : Set1 where
  constructor mkR
  field
    .fromR : Set

reflR : (r : R) -> r == r
reflR r = refl {a = _}
-- issue: unsolved metavars resolved 2010-10-15 by making eta-expansion
-- more lazy (do not eta expand all meta variable listeners, see MetaVars.hs