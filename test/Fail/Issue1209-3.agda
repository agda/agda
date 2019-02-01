-- This combination should not be allowed:

{-# OPTIONS --safe --guardedness --sized-types #-}

-- note that `--safe` turns off `--guardedness` and `--sized-types`,
-- hence `--guardedness --sized-types --safe` works, but does not
-- mean the above combination
