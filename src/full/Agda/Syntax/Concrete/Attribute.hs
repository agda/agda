
-- | Attributes: concrete syntax for ArgInfo, esp. modalities.

module Agda.Syntax.Concrete.Attribute where

import Control.Arrow (second)
import Control.Monad (foldM)

import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Concrete (Expr(..))
import Agda.Syntax.Concrete.Pretty () --instance only
import Agda.Syntax.Position

import Agda.Utils.Pretty (prettyShow)

-- import Agda.Utils.Functor

-- | An attribute is a modifier for `ArgInfo`.

data Attribute
  = RelevanceAttribute Relevance
  | QuantityAttribute  Quantity
  | TacticAttribute Expr
  | CohesionAttribute Cohesion
  deriving (Show)

instance HasRange Attribute where
  getRange = \case
    RelevanceAttribute r -> getRange r
    QuantityAttribute q  -> getRange q
    CohesionAttribute c  -> getRange c
    TacticAttribute e    -> getRange e

instance SetRange Attribute where
  setRange r = \case
    RelevanceAttribute a -> RelevanceAttribute $ setRange r a
    QuantityAttribute q  -> QuantityAttribute  $ setRange r q
    CohesionAttribute c  -> CohesionAttribute  $ setRange r c
    TacticAttribute e    -> TacticAttribute e  -- -- $ setRange r e -- SetRange Expr not yet implemented

instance KillRange Attribute where
  killRange = \case
    RelevanceAttribute a -> RelevanceAttribute $ killRange a
    QuantityAttribute q  -> QuantityAttribute  $ killRange q
    CohesionAttribute c  -> CohesionAttribute  $ killRange c
    TacticAttribute e    -> TacticAttribute    $ killRange e

-- | (Conjunctive constraint.)

type LensAttribute a = (LensRelevance a, LensQuantity a, LensCohesion a)

-- | Modifiers for 'Relevance'.

relevanceAttributeTable :: [(String, Relevance)]
relevanceAttributeTable = concat
  [ map (, Irrelevant)  [ "irr", "irrelevant" ]
  , map (, NonStrict)   [ "shirr", "shape-irrelevant" ]
  , map (, Relevant)    [ "relevant" ]
  ]

-- | Modifiers for 'Quantity'.

quantityAttributeTable :: [(String, Quantity)]
quantityAttributeTable =
  [ ("0"      , Quantity0 $ Q0       noRange)
  , ("erased" , Quantity0 $ Q0Erased noRange)
  -- TODO: linearity
  -- , ("1"      , Quantity1 $ Q1       noRange)
  -- , ("linear" , Quantity1 $ Q1Linear noRange)
  , ("ω"      , Quantityω $ Qω       noRange)
  , ("plenty" , Quantityω $ QωPlenty noRange)
  ]
-- quantityAttributeTable = concat
--   [ map (, Quantity0) [ "0", "erased" ] -- , "static", "compile-time" ]
--   , map (, Quantityω) [ "ω", "plenty" ] -- , "dynamic", "runtime", "unrestricted", "abundant" ]
--   -- , map (, Quantity1)  [ "1", "linear" ]
--   -- , map (, Quantity01) [ "01", "affine" ]
--   ]

cohesionAttributeTable :: [(String, Cohesion)]
cohesionAttributeTable =
  [ ("♭"    , Flat)
  , ("flat" , Flat)
  ]

-- | Concrete syntax for all attributes.

attributesMap :: Map String Attribute
attributesMap = Map.fromList $ concat
  [ map (second RelevanceAttribute) relevanceAttributeTable
  , map (second QuantityAttribute)  quantityAttributeTable
  , map (second CohesionAttribute)  cohesionAttributeTable
  ]

-- | Parsing a string into an attribute.

stringToAttribute :: String -> Maybe Attribute
stringToAttribute = (`Map.lookup` attributesMap)

-- | Parsing an expression into an attribute.

exprToAttribute :: Expr -> Maybe Attribute
exprToAttribute (Paren _ (RawApp _ [Tactic _ t])) = Just $ TacticAttribute t
exprToAttribute e = setRange (getRange e) $ stringToAttribute $ prettyShow e

-- | Setting an attribute (in e.g. an 'Arg').  Overwrites previous value.

setAttribute :: (LensAttribute a) => Attribute -> a -> a
setAttribute = \case
  RelevanceAttribute r -> setRelevance r
  QuantityAttribute  q -> setQuantity  q
  CohesionAttribute  c -> setCohesion  c
  TacticAttribute t    -> id


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
  | noUserQuantity a = Just $ setQuantity q a
  | otherwise = Nothing

-- | Setting 'Cohesion' if unset.

setPristineCohesion :: (LensCohesion a) => Cohesion -> a -> Maybe a
setPristineCohesion c a
  | getCohesion a == defaultCohesion = Just $ setCohesion c a
  | otherwise = Nothing

-- | Setting an unset attribute (to e.g. an 'Arg').

setPristineAttribute :: (LensAttribute a) => Attribute -> a -> Maybe a
setPristineAttribute = \case
  RelevanceAttribute r -> setPristineRelevance r
  QuantityAttribute  q -> setPristineQuantity  q
  CohesionAttribute  c -> setPristineCohesion  c
  TacticAttribute{}    -> Just

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

isTacticAttribute :: Attribute -> Maybe Expr
isTacticAttribute (TacticAttribute t) = Just t
isTacticAttribute _                   = Nothing

relevanceAttributes :: [Attribute] -> [Attribute]
relevanceAttributes = filter $ isJust . isRelevanceAttribute

quantityAttributes :: [Attribute] -> [Attribute]
quantityAttributes = filter $ isJust . isQuantityAttribute

tacticAttributes :: [Attribute] -> [Attribute]
tacticAttributes = filter $ isJust . isTacticAttribute
