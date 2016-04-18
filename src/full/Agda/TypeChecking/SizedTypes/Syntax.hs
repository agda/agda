{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Syntax of size expressions and constraints.

module Agda.TypeChecking.SizedTypes.Syntax where

import Data.Foldable (Foldable)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import Test.QuickCheck

import Agda.TypeChecking.SizedTypes.Utils

-- * Syntax

-- | Constant finite sizes @n >= 0@.
newtype Offset = O Int
  deriving (Eq, Ord, Num, Enum)

instance Show Offset where
  show (O n) = show n

instance MeetSemiLattice Offset where
  meet = min

instance Plus Offset Offset Offset where
  plus (O x) (O y) = O (plus x y)

instance Arbitrary Offset where
  arbitrary = do
    NonNegative x <- arbitrary
    return x

  shrink (O x) = map O $ filter (>= 0) (shrink x)

-- | Fixed size variables @i@.
newtype Rigid  = RigidId { rigidId :: String }
  deriving (Eq, Ord)

instance Show Rigid where show = rigidId

-- | Size meta variables @X@ to solve for.
newtype Flex   = FlexId { flexId :: String }
  deriving (Eq, Ord)

instance Show Flex where show = flexId

-- | Size expressions appearing in constraints.
data SizeExpr' rigid flex
  = Const { offset :: Offset }                   -- ^ Constant number @n@.
  | Rigid { rigid  :: rigid, offset :: Offset }  -- ^ Variable plus offset @i + n@.
  | Infty                                        -- ^ Infinity @∞@.
  | Flex  { flex   :: flex, offset :: Offset }   -- ^ Meta variable @X + n@.
    deriving (Eq, Ord, Functor, Foldable, Traversable)

type SizeExpr = SizeExpr' Rigid Flex

-- | Comparison operator, e.g. for size expression.
data Cmp
  = Lt  -- ^ @<@.
  | Le  -- ^ @≤@.
  deriving (Eq, Bounded, Enum)

instance Dioid Cmp where
  compose     = min
  unitCompose = Le

-- | Comparison operator is ordered @'Lt' < 'Le'@.
instance Ord Cmp where
  Lt <= x  = True
  Le <= Lt = False
  Le <= Le = True

instance MeetSemiLattice Cmp where
  meet = min

instance Top Cmp where
  top = Le

instance Arbitrary Cmp where
  arbitrary = arbitraryBoundedEnum

-- | Constraint: an inequation between size expressions,
--   e.g. @X < ∞@ or @i + 3 ≤ j@.
data Constraint' rigid flex = Constraint
  { leftExpr  :: SizeExpr' rigid flex
  , cmp       :: Cmp
  , rightExpr :: SizeExpr' rigid flex
  }
  deriving (Functor, Foldable, Traversable)

type Constraint = Constraint' Rigid Flex

-- * Polarities to specify solutions.
------------------------------------------------------------------------

-- | What type of solution are we looking for?
data Polarity = Least | Greatest
  deriving (Eq, Ord)

-- | Assigning a polarity to a flexible variable.
data PolarityAssignment flex = PolarityAssignment Polarity flex

-- | Type of solution wanted for each flexible.
type Polarities flex = Map flex Polarity

emptyPolarities :: Polarities flex
emptyPolarities = Map.empty

polaritiesFromAssignments :: Ord flex => [PolarityAssignment flex] -> Polarities flex
polaritiesFromAssignments = Map.fromList . map (\ (PolarityAssignment p x) -> (x,p))

-- | Default polarity is 'Least'.
getPolarity :: Ord flex => Polarities flex -> flex -> Polarity
getPolarity pols x = Map.findWithDefault Least x pols

-- * Solutions.
------------------------------------------------------------------------

-- | Partial substitution from flexible variables to size expression.
type Solution rigid flex = Map flex (SizeExpr' rigid flex)

-- emptySolution = Map.empty

-- | Executing a substitution.
class Substitute r f a where
  subst :: Solution r f -> a -> a

instance Ord f => Substitute r f (SizeExpr' r f) where
  subst sol e =
    case e of
      Flex x n -> Map.findWithDefault e x sol `plus` n
      _        -> e

instance Ord f => Substitute r f (Constraint' r f) where
  subst sol (Constraint e cmp e') = Constraint (subst sol e) cmp (subst sol e')

instance Substitute r f a => Substitute r f [a] where
  subst = map . subst

-- | Add offset to size expression.
instance Plus (SizeExpr' r f) Offset (SizeExpr' r f) where
  plus e m =
    case e of
      Const   n -> Const   $ n + m
      Rigid i n -> Rigid i $ n + m
      Flex x  n -> Flex x  $ n + m
      Infty     -> Infty

-- * Constraint simplification

type CTrans r f = Constraint' r f -> Either String [Constraint' r f]

-- | Returns an error message if we have a contradictory constraint.
simplify1 :: (Show f, Show r, Eq r) => CTrans r f -> CTrans r f
simplify1 test c = do
  let err = Left $ "size constraint " ++ show c ++ " is inconsistent"
  case c of
    -- rhs is Infty
    Constraint a           Le  Infty -> return []
    Constraint Const{}     Lt  Infty -> return []
    Constraint Infty       Lt  Infty -> err
    Constraint (Rigid i n) Lt  Infty -> test $ Constraint (Rigid i 0) Lt Infty
    Constraint a@Flex{}    Lt  Infty -> return [c { leftExpr = a { offset = 0 }}]

    -- rhs is Const
    Constraint (Const n)   cmp (Const m) -> if compareOffset n cmp m then return [] else err
    Constraint Infty       cmp  Const{}  -> err
    Constraint (Rigid i n) cmp (Const m) ->
      if compareOffset n cmp m then
        test (Constraint (Rigid i 0) Le (Const (m - n - ifLe cmp 0 1)))
       else err
    Constraint (Flex x n)  cmp (Const m) ->
      if compareOffset n cmp m
       then return [Constraint (Flex x 0) Le (Const (m - n - ifLe cmp 0 1))]
       else err

    -- rhs is Rigid
    Constraint Infty cmp Rigid{} -> err
    Constraint (Const m) cmp (Rigid i n) ->
      if compareOffset m cmp n then return []
      else test (Constraint (Const $ m - n) cmp (Rigid i 0))
    Constraint (Rigid j m) cmp (Rigid i n) | i == j ->
      if compareOffset m cmp n then return [] else err
    Constraint (Rigid j m) cmp (Rigid i n) -> test c
    Constraint (Flex x m)  cmp (Rigid i n) ->
      if compareOffset m cmp n
       then return [Constraint (Flex x 0) Le (Rigid i (n - m - ifLe cmp 0 1))]
       else return [Constraint (Flex x $ m - n + ifLe cmp 0 1) Le (Rigid i 0)]

    -- rhs is Flex
    Constraint Infty Le (Flex x n) -> return [Constraint Infty Le (Flex x 0)]
    Constraint Infty Lt (Flex x n) -> err
    Constraint (Const m) cmp (Flex x n) ->
      if compareOffset m cmp n then return []
      else return [Constraint (Const $ m - n + ifLe cmp 0 1) Le (Flex x 0)]
    Constraint (Rigid i m) cmp (Flex x n) ->
      if compareOffset m cmp n
      then return [Constraint (Rigid i 0) cmp (Flex x $ n - m)]
      else return [Constraint (Rigid i $ m - n) cmp (Flex x 0)]
    Constraint (Flex y m) cmp (Flex x n) ->
      if compareOffset m cmp n
      then return [Constraint (Flex y 0) cmp (Flex x $ n - m)]
      else return [Constraint (Flex y $ m - n) cmp (Flex x 0)]

-- | 'Le' acts as 'True', 'Lt' as 'False'.
ifLe :: Cmp -> a -> a -> a
ifLe Le a b = a
ifLe Lt a b = b

-- | Interpret 'Cmp' as relation on 'Offset'.
compareOffset :: Offset -> Cmp -> Offset -> Bool
compareOffset n Le m = n <= m
compareOffset n Lt m = n <  m

-- * Printing

instance (Show r, Show f) => Show (SizeExpr' r f) where
  show (Const n)   = show n
  show (Infty)     = "∞"
  show (Rigid i 0) = show i
  show (Rigid i n) = show i ++ "+" ++ show n
  show (Flex  x 0) = show x
  show (Flex  x n) = show x ++ "+" ++ show n

instance Show Polarity where
  show Least    = "-"
  show Greatest = "+"

instance Show flex => Show (PolarityAssignment flex) where
  show (PolarityAssignment pol flex) = show pol ++ show flex

instance Show Cmp where
  show Le = "≤"
  show Lt = "<"

instance (Show r, Show f) => Show (Constraint' r f) where
  show (Constraint a cmp b) = show a ++ " " ++ show cmp ++ " " ++ show b

-- * Wellformedness

-- | Offsets @+ n@ must be non-negative
class ValidOffset a where
  validOffset :: a -> Bool

instance ValidOffset Offset where
  validOffset = (>= 0)

instance ValidOffset (SizeExpr' r f) where
  validOffset e =
    case e of
      Infty -> True
      _     -> validOffset (offset e)

-- | Make offsets non-negative by rounding up.
class TruncateOffset a where
  truncateOffset :: a -> a

instance TruncateOffset Offset where
  truncateOffset n | n >= 0    = n
                   | otherwise = 0

instance TruncateOffset (SizeExpr' r f) where
  truncateOffset e =
    case e of
      Infty     -> e
      Const n   -> Const   $ truncateOffset n
      Rigid i n -> Rigid i $ truncateOffset n
      Flex  x n -> Flex  x $ truncateOffset n

-- * Computing variable sets

-- | The rigid variables contained in a pice of syntax.
class Rigids r a where
  rigids :: a -> Set r

instance (Ord r, Rigids r a) => Rigids r [a] where
  rigids as = Set.unions (map rigids as)

instance Rigids r (SizeExpr' r f) where
  rigids (Rigid x _) = Set.singleton x
  rigids _           = Set.empty

instance Ord r => Rigids r (Constraint' r f) where
  rigids (Constraint l _ r) = Set.union (rigids l) (rigids r)

-- | The flexibe variables contained in a pice of syntax.
class Flexs flex a | a -> flex where
  flexs :: a -> Set flex

instance (Ord flex, Flexs flex a) => Flexs flex [a] where
  flexs as = Set.unions (map flexs as)

instance Flexs flex (SizeExpr' rigid flex) where
  flexs (Flex x _) = Set.singleton x
  flexs _          = Set.empty

instance (Ord flex) => Flexs flex (Constraint' rigid flex) where
  flexs (Constraint l _ r) = Set.union (flexs l) (flexs r)
