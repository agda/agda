-- | Non-empty lists.
--
--   Better name @List1@ for non-empty lists, plus missing functionality.
--
--   Import:
--   @
--
--     {-# LANGUAGE PatternSynonyms #-}
--
--     import           Agda.Utils.List1 (List1, (:|))
--     import qualified Agda.Utils.List1 as List1
--
--   @

{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
  -- because of https://gitlab.haskell.org/ghc/ghc/issues/10339

module Agda.Utils.List1
  ( module NonEmpty
  , module Agda.Utils.List1
  ) where

import qualified Data.List.NonEmpty
import Data.List.NonEmpty as NonEmpty hiding (NonEmpty, (:|))

type List1 = Data.List.NonEmpty.NonEmpty

infixr 5 :|

pattern (:|) :: a -> [a] -> List1 a
pattern (:|) x xs = (Data.List.NonEmpty.:|) x xs

-- | Append a list to a non-empty list.

append :: List1 a -> [a] -> List1 a
append (x :| xs) ys = x :| mappend xs ys
