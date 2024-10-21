
-- | Attributes: concrete syntax for ArgInfo, esp. modalities.

module Agda.Syntax.Concrete.Attribute where

import Control.Arrow (second)
import Control.Monad (foldM)

import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Concrete (Expr(..), TacticAttribute)
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pretty () --instance only
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Position

import Agda.Utils.List1 (List1, pattern (:|))

import Agda.Utils.Impossible

-- | An attribute is a modifier for `ArgInfo`.

data Attribute
  = RelevanceAttribute Relevance
  | QuantityAttribute  Quantity
  | TacticAttribute (Ranged Expr)
  | CohesionAttribute Cohesion
  | PolarityAttribute PolarityModality
  | LockAttribute      Lock
  deriving (Show)

instance HasRange Attribute where
  getRange = \case
    RelevanceAttribute r -> getRange r
    QuantityAttribute q  -> getRange q
    CohesionAttribute c  -> getRange c
    PolarityAttribute p  -> getRange p
    TacticAttribute e    -> getRange e
    LockAttribute l      -> NoRange

instance SetRange Attribute where
  setRange r = \case
    RelevanceAttribute a -> RelevanceAttribute $ setRange r a
    QuantityAttribute q  -> QuantityAttribute  $ setRange r q
    CohesionAttribute c  -> CohesionAttribute  $ setRange r c
    PolarityAttribute p  -> PolarityAttribute  $ setRange r p
    TacticAttribute e    -> TacticAttribute e  -- -- $ setRange r e -- SetRange Expr not yet implemented
    LockAttribute l      -> LockAttribute l

instance KillRange Attribute where
  killRange = \case
    RelevanceAttribute a -> RelevanceAttribute $ killRange a
    QuantityAttribute q  -> QuantityAttribute  $ killRange q
    CohesionAttribute c  -> CohesionAttribute  $ killRange c
    PolarityAttribute p  -> PolarityAttribute  $ killRange p
    TacticAttribute e    -> TacticAttribute    $ killRange e
    LockAttribute l      -> LockAttribute l

-- | (Conjunctive constraint.)

type LensAttribute a = (LensRelevance a, LensQuantity a, LensCohesion a, LensModalPolarity a, LensLock a)

-- | Modifiers for 'Relevance'.

relevanceAttributeTable :: [(String, Relevance)]
relevanceAttributeTable =
  [ ("irr"             , Irrelevant      $ OIrrIrr               noRange)
  , ("irrelevant"      , Irrelevant      $ OIrrIrrelevant        noRange)
  , ("shirr"           , ShapeIrrelevant $ OShIrrShIrr           noRange)
  , ("shape-irrelevant", ShapeIrrelevant $ OShIrrShapeIrrelevant noRange)
  , ("relevant"        , Relevant        $ ORelRelevant          noRange)
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

-- | Information about attributes (attribute, range, printed
-- representation).
--
-- This information is returned by the parser. Code that calls the
-- parser should, if appropriate, complain if support for the given
-- attributes has not been enabled. This can be taken care of by
-- 'Agda.Syntax.Translation.ConcreteToAbstract.checkAttributes', which
-- should not be called until after pragma options have been set.

type Attributes = [(Attribute, Range, String)]

-- | Modifiers for 'Polarity'.

polarityAttributeTable :: [(String, PolarityModality)]
polarityAttributeTable =
  [ ("unused" , withStandardLock UnusedPolarity)
  , ("++" , withStandardLock StrictlyPositive)
  , ("+" , withStandardLock Positive)
  , ("-" , withStandardLock Negative)
  , ("mixed" , withStandardLock MixedPolarity)]

-- | Modifiers for 'Quantity'.

lockAttributeTable :: [(String, Lock)]
lockAttributeTable = concat
  [ map (, IsNotLock) [ "notlock" ] -- default, shouldn't be used much
  , map (, IsLock LockOTick) [ "tick" ] -- @tick
  , map (, IsLock LockOLock) [ "lock" ] -- @lock
  ]


-- | Concrete syntax for all attributes.

attributesMap :: Map String Attribute
attributesMap = Map.fromListWith __IMPOSSIBLE__ $ concat
  [ map (second RelevanceAttribute) relevanceAttributeTable
  , map (second QuantityAttribute)  quantityAttributeTable
  , map (second CohesionAttribute)  cohesionAttributeTable
  , map (second PolarityAttribute)  polarityAttributeTable
  , map (second LockAttribute)      lockAttributeTable
  ]

-- | Parsing a string into an attribute.

stringToAttribute :: String -> Maybe Attribute
stringToAttribute = (`Map.lookup` attributesMap)

-- | Parsing an expression into an attribute.

exprToAttribute :: Expr -> Maybe Attribute
exprToAttribute = \case
  e@(Paren _ (Tactic _ t)) -> Just $ TacticAttribute $ Ranged (getRange e) t
  e -> setRange (getRange e) $ stringToAttribute $ prettyShow e

-- | Setting an attribute (in e.g. an 'Arg').  Overwrites previous value.

setAttribute :: (LensAttribute a) => Attribute -> a -> a
setAttribute = \case
  RelevanceAttribute r -> setRelevance r
  QuantityAttribute  q -> setQuantity  q
  CohesionAttribute  c -> setCohesion  c
  PolarityAttribute  p -> setModalPolarity p
  LockAttribute      l -> setLock      l
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

-- | Setting 'ModalPolarity' if unset.

setPristinePolarity :: (LensModalPolarity a) => PolarityModality -> a -> Maybe a
setPristinePolarity c a
  | getModalPolarity a == defaultPolarity = Just $ setModalPolarity c a
  | otherwise = Nothing

-- | Setting 'Lock' if unset.

setPristineLock :: (LensLock a) => Lock -> a -> Maybe a
setPristineLock q a
  | getLock a == defaultLock = Just $ setLock q a
  | otherwise = Nothing

-- | Setting an unset attribute (to e.g. an 'Arg').

setPristineAttribute :: (LensAttribute a) => Attribute -> a -> Maybe a
setPristineAttribute = \case
  RelevanceAttribute r -> setPristineRelevance r
  QuantityAttribute  q -> setPristineQuantity  q
  CohesionAttribute  c -> setPristineCohesion  c
  PolarityAttribute  p -> setPristinePolarity  p
  LockAttribute      l -> setPristineLock      l
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

isTacticAttribute :: Attribute -> TacticAttribute
isTacticAttribute = C.TacticAttribute . \case
  TacticAttribute t -> Just t
  _ -> Nothing

relevanceAttributes :: [Attribute] -> [Attribute]
relevanceAttributes = filter $ isJust . isRelevanceAttribute

quantityAttributes :: [Attribute] -> [Attribute]
quantityAttributes = filter $ isJust . isQuantityAttribute

tacticAttributes :: [Attribute] -> [Attribute]
tacticAttributes = filter $ isJust . C.theTacticAttribute . isTacticAttribute
