-- | Non-empty sets.
--
--   Provides type @Set1@ of non-empty sets.
--
--   Import:
--   @
--
--     import           Agda.Utils.Set1 (Set1)
--     import qualified Agda.Utils.Set1 as Set1
--
--   @

module Agda.Utils.Set1
  ( module Agda.Utils.Set1
  , module Set1
  ) where

import Data.Set.NonEmpty as Set1

type Set1 = Set1.NESet
