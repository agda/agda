
-- | Attributes: concrete syntax for ArgInfo, esp. modalities.

module Agda.Syntax.Concrete.Attribute where

import Control.Arrow (second)
import Control.Monad (foldM)

import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name

-- import Agda.Utils.Functor

-- | An attribute is a modifier for `ArgInfo`.

data Attribute
  = RelevanceAttribute Relevance
  | QuantityAttribute  Quantity
  deriving (Eq, Ord, Show)

-- | (Conjunctive constraint.)

type LensAttribute a = (LensRelevance a, LensQuantity a)

-- | Modifiers for 'Relevance'.

relevanceAttributeTable :: [(String, Relevance)]
relevanceAttributeTable = concat
  [ map (, Irrelevant)  [ "irr", "irrelevant" ]
  , map (, NonStrict)   [ "shirr", "shape-irrelevant" ]
  , map (, Relevant)    [ "relevant" ]
  ]

-- | Modifiers for 'Quantity'.

quantityAttributeTable :: [(String, Quantity)]
quantityAttributeTable = concat
  [ map (, Quantity0) [ "0", "erased" ] -- , "static", "compile-time" ]
  , map (, Quantityω) [ "ω", "plenty" ] -- , "dynamic", "runtime", "unrestricted", "abundant" ]
  -- , map (, Quantity1)  [ "1", "linear" ]
  -- , map (, Quantity01) [ "01", "affine" ]
  ]

-- | Concrete syntax for all attributes.

attributesMap :: Map String Attribute
attributesMap = Map.fromList $ concat
  [ map (second RelevanceAttribute) relevanceAttributeTable
  , map (second QuantityAttribute)  quantityAttributeTable
  ]

-- | Parsing a string into an attribute.

stringToAttribute :: String -> Maybe Attribute
stringToAttribute = (`Map.lookup` attributesMap)

-- | Setting an attribute (in e.g. an 'Arg').  Overwrites previous value.

setAttribute :: (LensAttribute a) => Attribute -> a -> a
setAttribute = \case
  RelevanceAttribute r -> setRelevance r
  QuantityAttribute  q -> setQuantity  q


-- | Setting some attributes in left-to-right order.
--   Blindly overwrites previous settings.

setAttributes :: (LensAttribute a) => [Attribute] -> a -> a
setAttributes attrs arg = foldl' (flip setAttribute) arg attrs

---------------------------------------------------------------------------
-- * Applying attributes only if they have not been set already.
--   No overwriting.
---------------------------------------------------------------------------

-- | Setting 'Relevance' if unset.

setPristineRelevance :: (LensRelevance a) => Relevance -> a -> Maybe a
setPristineRelevance r a
  | getRelevance a == defaultRelevance = Just $ setRelevance r a
  | otherwise = Nothing

-- | Setting 'Quantity' if unset.

setPristineQuantity :: (LensQuantity a) => Quantity -> a -> Maybe a
setPristineQuantity q a
  | getQuantity a == defaultQuantity = Just $ setQuantity q a
  | otherwise = Nothing

-- | Setting an unset attribute (to e.g. an 'Arg').

setPristineAttribute :: (LensAttribute a) => Attribute -> a -> Maybe a
setPristineAttribute = \case
  RelevanceAttribute r -> setPristineRelevance r
  QuantityAttribute  q -> setPristineQuantity  q

-- | Setting a list of unset attributes.

setPristineAttributes :: (LensAttribute a) => [Attribute] -> a -> Maybe a
setPristineAttributes attrs arg = foldM (flip setPristineAttribute) arg attrs

---------------------------------------------------------------------------
-- * Filtering attributes
---------------------------------------------------------------------------

isRelevanceAttribute :: Attribute -> Maybe Relevance
isRelevanceAttribute = \case
  RelevanceAttribute q -> Just q
  _ -> Nothing

isQuantityAttribute :: Attribute -> Maybe Quantity
isQuantityAttribute = \case
  QuantityAttribute q -> Just q
  _ -> Nothing

relevanceAttributes :: [Attribute] -> [Attribute]
relevanceAttributes = filter $ isJust . isRelevanceAttribute

quantityAttributes :: [Attribute] -> [Attribute]
quantityAttributes = filter $ isJust . isQuantityAttribute
