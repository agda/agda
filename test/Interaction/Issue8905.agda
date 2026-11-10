-- Issue #8905: after loading from an .agdai file, top-level commands
-- forgot the parameters of the top-level module.

module Issue8905 (A : Set) where

data D : Set where
  d : A → D
