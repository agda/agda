
module _ where

open import DeadCodePatSyn.Lib

-- Check that pattern synonyms count when computing dead code
f : _ → Set₁
f not-hidden = Set
