-- Andreas, 2013-10-21 reported by Christian Sattler
{-# OPTIONS --allow-unsolved-metas #-}
module Issue922 where

import Common.Level

f : Set → Set → Set
f x _ = x   -- Note: second argument is unused

module _ (_ : f ? ?) where
  g = f
  -- Here an instance search for the unused argument (2nd ?)
  -- is triggered.

-- Problem WAS: instance search was started in wrong context.
