-- Andreas, 2014-10-23

data Bool : Set where
  true false : Bool

module _ (b : Bool) where

  f : Set
  f = {!b!}

-- Agda produces garbage when splitting on b.
-- Splitting on module parameters should be forbidden outright.
