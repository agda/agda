{-# OPTIONS --cohesion #-}
{-# OPTIONS --polarity #-}

-- Andreas, 2016-02-11. Irrelevant constructors are not (yet?) supported

data D : Set where
  .c : D

-- warning: -W[no]FixingRelevance

-- Andreas, 2018-06-14, issue #2513, surviving shape-irrelevance annotations.

data Wrap (A : Set) : Set where
  @shape-irrelevant wrap : A → Wrap A

-- Andreas, 2025-05-03, we should also check for other modality annotations.

data DC : Set where
  @♭    c1 : DC
  @flat c2 : DC

data DP : Set where
  @++     psp : DP
  @+      pp  : DP
  @-      pn  : DP
  @unused pu  : DP

data Ok : Set where
  @relevant   or : Ok
  @mixed      op : Ok
  -- @continuous oc : Ok  -- @continuous is not defined (yet)
