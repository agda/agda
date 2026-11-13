-- Ting-Gian, 2026-11-10, issue #8905

module Issue8905 (A : Set) where

data D : Set where
  d : A → D

-- Issue8905.sh first type-checks this module in batch mode, which writes
-- Issue8905.agdai.  It then starts --interaction, which loads the module
-- from that interface, and infers D, d and D → D with Cmd_infer_toplevel.

-- WAS: the top-level commands forgot the module parameter A:
-- D was inferred as (A₁ : Set) → Set, d as _A_2 → D,
-- and D → D failed with ShouldBeASort.

-- Should succeed now: D : Set, d : A → D and D → D : Set.
