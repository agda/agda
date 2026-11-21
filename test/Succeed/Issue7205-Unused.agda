-- Andreas, 2026-11-21, while working on issue #7205
-- Make sure that unused arguments are omitted in positivity checking.
-- We consider four possible variants of a constant endofunctor F:
-- - meta with @unused argument polarity
-- - postulate ditto
-- - postulate with POLARITY pragma
-- - module parameter

{-# OPTIONS --polarity --allow-unsolved-metas #-}

module Issue7205-Unused (A : Set) where

module WithHole where

  F : @unused Set → Set
  F = ?

  mutual
    data D : Set where
      hidden  : F (G D) → D
      visible : G A → D

    G : Set → Set
    G X = X → A

module WithPostulate where

  postulate F : @unused Set → Set

  mutual
    data D : Set where
      hidden  : F (G D) → D
      visible : G A → D

    G : Set → Set
    G X = X → A

module WithPolarityPragma where

  postulate F : Set → Set
  {-# POLARITY F _ #-}

  mutual
    data D : Set where
      hidden  : F (G D) → D
      visible : G A → D

    G : Set → Set
    G X = X → A

module WithModuleParameter (F : @unused Set → Set) where

  mutual
    data D : Set where
      hidden  : F (G D) → D
      visible : G A → D

    G : Set → Set
    G X = X → A

-- All should succeed.
