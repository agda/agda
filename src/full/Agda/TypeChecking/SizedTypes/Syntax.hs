{-# OPTIONS_GHC -Wunused-imports #-}

-- | Syntax of size expressions and constraints.

module Agda.TypeChecking.SizedTypes.Syntax where

import Prelude hiding ( null )


import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.TypeChecking.Monad.Base (TCM)
import qualified Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.SizedTypes.Utils

import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty

import Agda.Utils.Impossible

-- * Syntax

-- | Constant finite sizes @n >= 0@.
newtype Offset = O Int
  deriving (Eq, Ord, Num, Enum)

-- This Show instance is ok because of the Num constraint.
instance Show Offset where
  show (O n) = show n

instance Pretty Offset where
  pretty (O n) = pretty n

instance MeetSemiLattice Offset where
  meet = min

instance Plus Offset Offset Offset where
  plus (O x) (O y) = O (plus x y)

-- | Fixed size variables @i@.
newtype Rigid  = RigidId { rigidId :: String }
  deriving (Eq, Ord)

instance Show Rigid where
  show (RigidId s) = "RigidId " ++ show s

instance Pretty Rigid where
  pretty = text . rigidId

-- | Size meta variables @X@ to solve for.
newtype Flex   = FlexId { flexId :: String }
  deriving (Eq, Ord)

instance Show Flex where
  show (FlexId s) = "FlexId " ++ show s

instance Pretty Flex where
  pretty = text . flexId

instance P.PrettyTCM Flex where
  prettyTCM = return . pretty

-- | Size expressions appearing in constraints.
data SizeExpr' rigid flex
  = Const { offset :: Offset }                   -- ^ Constant number @n@.
  | Rigid { rigid  :: rigid, offset :: Offset }  -- ^ Variable plus offset @i + n@.
  | Infty                                        -- ^ Infinity @∞@.
  | Flex  { flex   :: flex, offset :: Offset }   -- ^ Meta variable @X + n@.
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type SizeExpr = SizeExpr' Rigid Flex

-- | Comparison operator, e.g. for size expression.
data Cmp
  = Lt  -- ^ @<@.
  | Le  -- ^ @≤@.
  deriving (Show, Eq, Bounded, Enum)

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

-- | Constraint: an inequation between size expressions,
--   e.g. @X < ∞@ or @i + 3 ≤ j@.
data Constraint' rigid flex = Constraint
  { leftExpr  :: SizeExpr' rigid flex
  , cmp       :: Cmp
  , rightExpr :: SizeExpr' rigid flex
  }
  deriving (Show, Functor, Foldable, Traversable)

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

-- Used in size-solver (Andreas, 2021-08-20)
polaritiesFromAssignments :: Ord flex => [PolarityAssignment flex] -> Polarities flex
polaritiesFromAssignments = Map.fromListWith __IMPOSSIBLE__ . map (\ (PolarityAssignment p x) -> (x,p))

-- | Default polarity is 'Least'.
getPolarity :: Ord flex => Polarities flex -> flex -> Polarity
getPolarity pols x = Map.findWithDefault Least x pols

-- * Solutions.
------------------------------------------------------------------------

-- | Partial substitution from flexible variables to size expression.
newtype Solution rigid flex = Solution { theSolution :: Map flex (SizeExpr' rigid flex) }
  deriving (Show, Null)

instance (Pretty r, Pretty f) => Pretty (Solution r f) where
  pretty (Solution sol) = prettyList $ for (Map.toList sol) $ \ (x, e) ->
    pretty x <+> ":=" <+> pretty e

emptySolution :: Solution r f
emptySolution = Solution Map.empty

-- | Executing a substitution.
class Substitute r f a where
  subst :: Solution r f -> a -> a

instance Ord f => Substitute r f (SizeExpr' r f) where
  subst (Solution sol) e =
    case e of
      Flex x n -> maybe e (`plus` n) $ Map.lookup x sol
      _        -> e

instance Ord f => Substitute r f (Constraint' r f) where
  subst sol (Constraint e cmp e') = Constraint (subst sol e) cmp (subst sol e')

instance Substitute r f a => Substitute r f [a] where
  subst = map . subst

instance Substitute r f a => Substitute r f (Map k a) where
  subst = fmap . subst

instance Ord f => Substitute r f (Solution r f) where
  subst s = Solution . subst s . theSolution

-- | Add offset to size expression.
instance Plus (SizeExpr' r f) Offset (SizeExpr' r f) where
  plus e m =
    case e of
      Const   n -> Const   $ n + m
      Rigid i n -> Rigid i $ n + m
      Flex x  n -> Flex x  $ n + m
      Infty     -> Infty

-- | Error messages produced by the constraint simplification monad.

type Error = TCM Doc

-- * Constraint simplification

type CTrans r f = Constraint' r f -> Either Error [Constraint' r f]

-- | Returns an error message if we have a contradictory constraint.
simplify1 :: (Pretty f, Pretty r, Eq r) => CTrans r f -> CTrans r f
simplify1 test c = do
  let err = Left $ "size constraint" P.<+> P.pretty c P.<+>
                   "is inconsistent"
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

instance (Pretty r, Pretty f) => Pretty (SizeExpr' r f) where
  pretty (Const n)   = pretty n
  pretty (Infty)     = "∞"
  pretty (Rigid i 0) = pretty i
  pretty (Rigid i n) = pretty i <> text ("+" ++ show n)
  pretty (Flex  x 0) = pretty x
  pretty (Flex  x n) = pretty x <> text ("+" ++ show n)

instance Pretty Polarity where
  pretty Least    = "-"
  pretty Greatest = "+"

instance Pretty flex => Pretty (PolarityAssignment flex) where
  pretty (PolarityAssignment pol flex) = pretty pol <> pretty flex

instance Pretty Cmp where
  pretty Le = "≤"
  pretty Lt = "<"

instance (Pretty r, Pretty f) => Pretty (Constraint' r f) where
  pretty (Constraint a cmp b) = pretty a <+> pretty cmp <+> pretty b

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
class Ord (RigidOf a) => Rigids a where
  type RigidOf a
  rigids :: a -> Set (RigidOf a)

instance Rigids a => Rigids [a] where
  type RigidOf [a] = RigidOf a
  rigids as = Set.unions (map rigids as)

instance Ord r => Rigids (SizeExpr' r f) where
  type RigidOf (SizeExpr' r f) = r
  rigids (Rigid x _) = Set.singleton x

  rigids _           = Set.empty

instance Ord r => Rigids (Constraint' r f) where
  type RigidOf (Constraint' r f) = r
  rigids (Constraint l _ r) = Set.union (rigids l) (rigids r)

-- | The flexibe variables contained in a pice of syntax.
class Ord (FlexOf a) => Flexs a where
  type FlexOf a
  flexs :: a -> Set (FlexOf a)

instance Flexs a => Flexs [a] where
  type FlexOf [a] = FlexOf a
  flexs as = Set.unions (map flexs as)

instance Ord flex => Flexs (SizeExpr' rigid flex) where
  type FlexOf (SizeExpr' rigid flex) = flex
  flexs (Flex x _) = Set.singleton x
  flexs _          = Set.empty

instance Ord flex => Flexs (Constraint' rigid flex) where
  type FlexOf (Constraint' rigid flex) = flex
  flexs (Constraint l _ r) = Set.union (flexs l) (flexs r)
