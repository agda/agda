-- Andreas, 2025-07-03, issue #7977:
-- Dead code warning instead of hard fail for unknown polarity.

postulate
  F : Set → Set

{-# POLARITY F ⚄ #-}

-- This pragma is dead code, since the only given polarity is unknown.
