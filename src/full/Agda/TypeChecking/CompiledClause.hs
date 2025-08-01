{-# OPTIONS_GHC -Wunused-imports #-}

-- | Case trees.
--
--   After coverage checking, pattern matching is translated
--   to case trees, i.e., a tree of successive case splits
--   on one variable at a time.

module Agda.TypeChecking.CompiledClause where

import Prelude hiding (null)

import Control.DeepSeq

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Semigroup (Any(..))

import GHC.Generics (Generic)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.Utils.Null
import Agda.Syntax.Common.Pretty

import Agda.Utils.Impossible

-- | The number of a 'Clause' (starting with 0) in the clause list of a 'FunctionData'.
type ClauseNumber = Int

data WithArity c = WithArity { arity :: Int, content :: c }
  deriving (Functor, Foldable, Traversable, Show, Generic)

-- | Branches in a case tree.

data Case c = Branches
  { projPatterns   :: Bool
    -- ^ We are constructing a record here (copatterns).
    --   'conBranches' lists projections.
  , conBranches    :: Map QName (WithArity c)
    -- ^ Map from constructor (or projection) names to their arity
    --   and the case subtree.  (Projections have arity 0.)
  , etaBranch      :: Maybe (ConHead, WithArity c)
    -- ^ Eta-expand with the given (eta record) constructor. If this is
    --   present, there should not be any conBranches or litBranches.
  , litBranches    :: Map Literal c
    -- ^ Map from literal to case subtree.
  , catchallBranch :: Maybe c
    -- ^ (Possibly additional) catch-all clause.
  , fallThrough :: Maybe Bool
    -- ^ (if True) In case of non-canonical argument use catchallBranch.
  , lazyMatch :: Bool
    -- ^ Lazy pattern match. Requires single (non-copattern) branch with no lit
    --   branches and no catch-all.
  }
  deriving (Functor, Foldable, Traversable, Show, Generic)

type CompiledClauses = CompiledClauses' Term

-- | Case tree with bodies.

data CompiledClauses' a
  = Case (Arg Int) (Case (CompiledClauses' a))
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
    -- If the @n@-th argument is a projection, we have only 'conBranches'
    -- with arity 0.
  | Done_ (CCDone a)
  | Fail [Arg ArgName]
    -- ^ Absurd case. Add the free variables here as well so we can build correct
    --   number of lambdas for strict backends. (#4280)
  deriving (Functor, Traversable, Foldable, Show, Generic)

{-# COMPLETE Case, Done, Fail #-}

-- | Data stored in 'Done' nodes of the case tree.
--  @CCDone no mr xs b@ stands for the body @b@ where the @xs@ contains hiding
--   and name suggestions for the free variables. This is needed to build
--   lambdas on the right hand side for partial applications which can
--   still reduce.
--   The @no@ is the number of the original 'Clause' this case tree leaf comes from.
--   @mr@ tells whether this body contains calls to the mutually recursive functions.
data CCDone a = CCDone
  { ccClauseNumber    :: ClauseNumber
  , ccClauseRecursive :: ClauseRecursive
  , ccBoundVars       :: [Arg ArgName]
  , ccBody            :: a
  }
  deriving (Functor, Traversable, Foldable, Show, Generic)

pattern Done :: ClauseNumber -> ClauseRecursive -> [Arg ArgName] -> a -> CompiledClauses' a
pattern Done no mr xs b = Done_ (CCDone no mr xs b)

litCase :: Literal -> c -> Case c
litCase l x = Branches False Map.empty Nothing (Map.singleton l x) Nothing (Just False) False

conCase :: QName -> Bool -> WithArity c -> Case c
conCase c b x = Branches False (Map.singleton c x) Nothing Map.empty Nothing (Just b) False

etaCase :: ConHead -> WithArity c -> Case c
etaCase c x = Branches False Map.empty (Just (c, x)) Map.empty Nothing (Just False) True

projCase :: QName -> c -> Case c
projCase c x = Branches True (Map.singleton c $ WithArity 0 x) Nothing Map.empty Nothing (Just False) False

catchall :: c -> Case c
catchall x = Branches False Map.empty Nothing Map.empty (Just x) (Just True) False

-- | Check that the requirements on lazy matching (single inductive case) are
--   met, and set lazy to False otherwise.
checkLazyMatch :: Case c -> Case c
checkLazyMatch b = b { lazyMatch = lazyMatch b && requirements }
  where
    requirements = and
      [ null (catchallBranch b)
      , Map.size (conBranches b) <= 1
      , null (litBranches b)
      , not $ projPatterns b ]

-- | Check whether a case tree has a catch-all clause.
hasCatchall :: CompiledClauses -> Bool
hasCatchall = getAny . loop
  where
  loop cc = case cc of
    Fail{}    -> mempty
    Done{}    -> mempty
    Case _ br -> maybe (foldMap loop br) (const $ Any True) $ catchallBranch br

-- | Check whether a case tree has any projection patterns
hasProjectionPatterns :: CompiledClauses -> Bool
hasProjectionPatterns = getAny . loop
  where
  loop cc = case cc of
    Fail{}    -> mempty
    Done{}    -> mempty
    Case _ br -> Any (projPatterns br) <> foldMap loop br

---------------------------------------------------------------------------
-- * Traversing the 'Done' leaves

class MapDone f where
  mapDone :: (CCDone a -> CCDone b) -> f a -> f b

-- instance MapDone CCDone where
--   mapDone = id

instance MapDone CompiledClauses' where
  mapDone f = \case
    Case n bs  -> Case n $ fmap (mapDone f) bs
    Done_ done -> Done_ $ f done
    Fail xs    -> Fail xs

---------------------------------------------------------------------------
-- Collection instances

instance Semigroup c => Semigroup (WithArity c) where
  WithArity n1 c1 <> WithArity n2 c2
    | n1 == n2  = WithArity n1 (c1 <> c2)
    | otherwise = __IMPOSSIBLE__   -- arity must match!

instance (Semigroup c, Monoid c) => Monoid (WithArity c) where
  mempty  = WithArity __IMPOSSIBLE__ mempty
  mappend = (<>)

instance Semigroup m => Semigroup (Case m) where
  Branches cop cs eta ls m b lazy <> Branches cop' cs' eta' ls' m' b' lazy' = checkLazyMatch $
    Branches (cop || cop') -- for @projCase <> mempty@
             (Map.unionWith (<>) cs cs')
             (unionEta eta eta')
             (Map.unionWith (<>) ls ls')
             (m <> m')
             (combine b b')
             (lazy && lazy')
   where
     combine Nothing  b'        = b
     combine b        Nothing   = b
     combine (Just b) (Just b') = Just $ b && b'

     unionEta Nothing b = b
     unionEta b Nothing = b
     unionEta Just{} Just{} = __IMPOSSIBLE__

instance (Semigroup m, Monoid m) => Monoid (Case m) where
  mempty  = empty
  mappend = (<>)

instance Null (Case m) where
  empty = Branches False Map.empty Nothing Map.empty Nothing Nothing True
  null (Branches _cop cs eta ls mcatch _b _lazy) = null cs && null eta && null ls && null mcatch

---------------------------------------------------------------------------
-- Pretty instances

instance Pretty a => Pretty (WithArity a) where
  pretty = pretty . content

instance Pretty a => Pretty (Case a) where
  prettyPrec p (Branches _cop cs eta ls m b lazy) =
    mparens (p > 0) $ prLazy lazy <+> vcat (prettyMap_ cs ++ prEta eta ++ prettyMap_ ls ++ prC m)
    where
      prLazy True  = "~"
      prLazy False = empty
      prC Nothing = []
      prC (Just x) = ["_ ->" <+> pretty x]
      prEta Nothing = []
      prEta (Just (c, cc)) = [("eta" <+> pretty c <+> "->") <?> pretty cc]

prettyMap_ :: (Pretty k, Pretty v) => Map k v -> [Doc]
prettyMap_ = map prettyAssign . Map.toList

instance Pretty a => Pretty (CompiledClauses' a) where
  pretty (Done_ done) = pretty done
  pretty Fail{}       = "fail"
  pretty (Case n bs) | projPatterns bs =
    sep [ "record"
        , nest 2 $ pretty bs
        ]
  pretty (Case n bs) =
    text ("case " ++ prettyShow n ++ " of") <?> pretty bs

instance Pretty a => Pretty (CCDone a) where
  pretty (CCDone no mr xs t) = ("done" <+> (pretty no <> pretty mr <> ":") <+> pretty xs) <?> prettyPrec 10 t

---------------------------------------------------------------------------
-- KillRange instances

instance KillRange c => KillRange (WithArity c) where
  killRange = fmap killRange

instance KillRange c => KillRange (Case c) where
  killRange (Branches cop con eta lit all b lazy) = Branches cop
    (killRangeMap con)
    (killRange eta)
    (killRangeMap lit)
    (killRange all)
    b lazy

instance KillRange CompiledClauses where
  killRange (Case i br)       = killRangeN Case i br
  killRange (Done no mr xs v) = killRangeN Done no mr xs v
  killRange (Fail xs)         = killRangeN Fail xs

---------------------------------------------------------------------------
-- TermLike instances

instance TermLike a => TermLike (WithArity a) where
  traverseTermM = traverse . traverseTermM
  foldTerm      = foldMap . foldTerm

instance TermLike a => TermLike (Case a) where
  traverseTermM = traverse . traverseTermM
  foldTerm      = foldMap . foldTerm

instance TermLike a => TermLike (CompiledClauses' a) where
  traverseTermM = traverse . traverseTermM
  foldTerm      = foldMap . foldTerm

instance TermLike a => TermLike (CCDone a) where
  traverseTermM = traverse . traverseTermM
  foldTerm      = foldMap . foldTerm

---------------------------------------------------------------------------
-- NFData instances

instance NFData c => NFData (WithArity c)
instance NFData a => NFData (Case a)
instance NFData a => NFData (CompiledClauses' a)
instance NFData a => NFData (CCDone a)
