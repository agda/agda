
{-# LANGUAGE Strict #-}
-- {-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

module Agda.TypeChecking.Positivity.NewOccurrence where

import Prelude hiding ( null, (!!) )

import Control.Applicative hiding (empty)
import Control.DeepSeq

import Data.Either
import qualified Data.Foldable as Fold
import Data.Function (on)
import Data.Graph (SCC(..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as DS
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Strict.These

import Agda.Interaction.Options.Base (optOccurrence, optPolarity)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position (HasRange(..), noRange)
import Agda.TypeChecking.Datatypes ( isDataOrRecordType )
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Monad hiding (getOccurrencesFromType)
import Agda.TypeChecking.Monad.Benchmark (MonadBench, Phase)
import Agda.TypeChecking.Monad.Benchmark qualified as Bench
import Agda.TypeChecking.Patterns.Match ( properlyMatching )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Positivity.Occurrence (Occurrence(..), modalPolarityToOccurrence)

import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.Function (applyUnless)
import Agda.Utils.Functor
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common.Pretty (Pretty, prettyShow)
import Agda.Utils.SemiRing
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.StrictReader
import Agda.Utils.StrictState
import Agda.Utils.Map qualified as Map

import Agda.Utils.Impossible

import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import Agda.Utils.Graph.AdjacencyMap.Unidirectional qualified as Graph

--------------------------------------------------------------------------------

data Path
  = Root
  | LeftOfArrow Path
  | DefArg Path QName Nat         -- ^ in the nth argument of a defined constant
  | UnderInf Path                 -- ^ in the principal argument of built-in ∞
  | VarArg Path Nat               -- ^ as an argument to a bound variable.
  | MetaArg Path                  -- ^ as an argument of a metavariable
  | ConArgType Path QName         -- ^ in the type of a constructor
  | IndArgType Path QName         -- ^ in a datatype index of a constructor
  | ConEndpoint Path QName        -- ^ in an endpoint of a higher constructor
  | InClause Path Nat             -- ^ in the nth clause of a defined function
  | Matched Path                  -- ^ matched against in a clause of a defined function
  | IsIndex Path                  -- ^ is an index of an inductive family
  | InDefOf Path QName            -- ^ in the definition of a constant
  deriving (Eq, Ord, Show)

data Node = DefNode QName | ArgNode QName Nat
  deriving (Eq, Ord)

-- | Top-level arg index that a local variable was bound in, arg polarity of the var itself.
data DefArgInEnv = DefArgInEnv Int [Occurrence]

data OccEnv = OccEnv {
    topDef     :: QName         -- ^ The definition we're working under.
  , topDefArgs :: [DefArgInEnv] -- ^ Occurrence info for definitions args.
  , inf        :: Maybe QName   -- ^ Name for ∞ builtin.
  , locals     :: Int           -- ^ Number of local binders (on the top of the definition args).
  , mutuals    :: Set QName     -- ^ Definitions in the current mutual group.
  , target     :: Node          -- ^ We add occurrences pointing to this node.
  , path       :: Path          -- ^ Path from the target node to the current position.
  , occ        :: Occurrence    -- ^ Occurence of current position.
  }

data Edge     = Edge Occurrence Path
type OccGraph = Map Node (Map Node Edge)
type OccM     = ReaderT OccEnv (StateT OccGraph TCM)

mergeEdges :: Edge -> Edge -> Edge
mergeEdges _                    e@(Edge Mixed _)     = e -- dominant
mergeEdges e@(Edge Mixed _)     _                    = e
mergeEdges (Edge Unused _)      e                    = e -- neutral
mergeEdges e                    (Edge Unused _)      = e
mergeEdges (Edge JustNeg _)     e@(Edge JustNeg _)   = e
mergeEdges _                    e@(Edge JustNeg p)   = Edge Mixed p
mergeEdges e@(Edge JustNeg p)   _                    = Edge Mixed p
mergeEdges _                    e@(Edge JustPos _)   = e -- dominates strict pos.
mergeEdges e@(Edge JustPos _)   _                    = e
mergeEdges _                    e@(Edge StrictPos _) = e -- dominates 'GuardPos'
mergeEdges e@(Edge StrictPos _) _                    = e
mergeEdges (Edge GuardPos _)    e@(Edge GuardPos _)  = e

{-# INLINE underPath #-}
underPath :: (Path -> Path) -> OccM a -> OccM a
underPath f = local \env -> env {path = f (path env)}

{-# INLINE underOcc #-}
underOcc :: Occurrence -> OccM a -> OccM a
underOcc p = local \env -> env {occ = otimes (occ env) p}

{-# INLINE underBinder #-}
underBinder :: OccM a -> OccM a
underBinder = local \env -> env {locals = locals env + 1}

{-# INLINE underPathOcc #-}
underPathOcc :: (Path -> Path) -> Occurrence -> OccM a -> OccM a
underPathOcc f p = underPath f . underOcc p

getOccurrencesFromType :: Type -> TCM [Occurrence]
getOccurrencesFromType a = (optPolarity <$> pragmaOptions) >>= \case
  False -> pure []
  True  -> do
    let go :: Type -> ReduceM [Occurrence]
        go a = (unEl <$> reduce a) >>= \case
          Pi a b -> do
            let p = modalPolarityToOccurrence $ modPolarityAnn $ getModalPolarity a
            ~ps <- go (unAbs b) -- lazy because we might have fewer args in Elims than Pi args
            pure (p:ps)
          _ -> pure []
    liftReduce (go a)

addEdge :: Node -> OccM ()
addEdge src = do
  target <- asks target
  path   <- asks path
  occ    <- asks occ
  let e = Edge occ path
  modify $ Map.insertWithGood
    (\_ -> Map.insertWithGood mergeEdges target e)
    src
    (Map.singleton target e)

occurrencesInDefArg :: QName -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArg d p i e =
  underOcc p $ underPath (\p -> DefArg p d i) $ occurrences e

occurrencesInDefArgArg :: Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArgArg p i e =
  underOcc p $ underPath (`VarArg` i) $ occurrences e

occurrencesInMutDefArg :: QName -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInMutDefArg d p i e =
  underOcc p $ underPath (\p -> DefArg p d i) $ do
    let newNode = ArgNode d i
    addEdge newNode  -- add edge from argument node to target
    local (\e -> e {path = Root, target = newNode}) do -- retarget to argument node
      occurrences e

class ComputeOccurrences a where
  occurrences :: a -> OccM ()

  {-# INLINE occurrences #-}
  default occurrences :: (Foldable t, ComputeOccurrences b, a ~ t b) => a -> OccM ()
  occurrences = mapM_ occurrences

instance ComputeOccurrences Term where
  occurrences t = case unSpine t of

    Var x es -> do
      locals <- asks locals

      -- it's a locally bound variable, all args are Mixed occurrence
      if x < locals then do
        let elims i []     = pure ()
            elims i (e:es) = underPath (`VarArg` i) (occurrences e) >> elims (i + 1) es
        underOcc Mixed $ elims 0 es

      -- it's bound in a top-level definition argument
      else do
        let elims i _      []     = pure ()
            elims i []     (e:es) = occurrencesInDefArgArg Mixed i e >> elims (i + 1) [] es
            elims i (p:ps) (e:es) = occurrencesInDefArgArg p i e     >> elims (i + 1) ps es
        topDefArgs <- asks topDefArgs
        topDef     <- asks topDef
        let DefArgInEnv argix ps = topDefArgs !! (x - locals)
        addEdge (ArgNode topDef argix)
        elims 0 ps es

    Def d es -> asks inf >>= \case

      Just inf | d == inf -> do
        error "TODO: handle inf in occurrence"

      _ -> do
        mutuals <- asks mutuals
        def <- liftTCM $ getConstInfo d

        -- it's a mutual definition
        if Set.member d mutuals then do
          addEdge (DefNode d)
          case theDef def of
            Constructor{} -> do
              let elims i []     = pure ()
                  elims i (e:es) = do occurrencesInMutDefArg d StrictPos i e
                                      elims (i + 1) es
              elims 0 es

            _ -> do
              let elims' :: QName -> Int -> [Occurrence] -> Elims -> OccM ()
                  elims' d i _      []     = pure ()
                  elims' d i (p:ps) (e:es) = do occurrencesInMutDefArg d p i e
                                                elims' d (i + 1) ps es
                  elims' _ _ _      _      = __IMPOSSIBLE__

              let elims :: QName -> Type -> Int -> [Occurrence] -> Elims -> OccM ()
                  elims d a i _      []     = pure ()
                  elims d a i (p:ps) (e:es) = do occurrencesInMutDefArg d p i e
                                                 elims d a (i + 1) ps es
                  elims d a i []     (e:es) = do ps <- liftTCM $ getOccurrencesFromType a
                                                 elims' d i (drop i ps) (e:es)

              elims d (defType def) 0 (defArgOccurrences def) es

        -- not a mutual definition
        else case theDef def of

          Constructor{} -> do
            let elims i []     = pure ()
                elims i (e:es) = do occurrencesInDefArg d StrictPos i e
                                    elims (i + 1) es
            elims 0 es

          _ -> do
            let elims' :: QName -> Int -> [Occurrence] -> Elims -> OccM ()
                elims' d i _      []     = pure ()
                elims' d i (p:ps) (e:es) = do occurrencesInMutDefArg d p i e
                                              elims' d (i + 1) ps es
                elims' _ _ _      _      = __IMPOSSIBLE__

            let elims :: QName -> Type -> Int -> [Occurrence] -> Elims -> OccM ()
                elims d a i _      []     = pure ()
                elims d a i (p:ps) (e:es) = do occurrencesInMutDefArg d p i e
                                               elims d a (i + 1) ps es
                elims d a i []     (e:es) = do ps <- liftTCM $ getOccurrencesFromType a
                                               elims' d i (drop i ps) (e:es)

            elims d (defType def) 0 (defArgOccurrences def) es

    Con _ _ es -> occurrences es -- András 2026-02-17: why?
    MetaV _ es -> underPathOcc MetaArg Mixed (occurrences es)
    Pi a b     -> underPathOcc LeftOfArrow JustNeg (occurrences a) >> occurrences b
    Lam _ t    -> occurrences t
    Level l    -> occurrences l
    Lit{}      -> pure ()
    Sort{}     -> pure ()
    -- Jesper, 2020-01-12: this information is also used for the
    -- occurs check, so we need to look under DontCare (see #4371)
    DontCare t -> occurrences t
    Dummy{}    -> pure ()

instance ComputeOccurrences Clause where
  occurrences cl = do
    let ps = namedClausePats cl
    -- TODO #3733: handle hcomp/transp clauses properly
    if hasDefP ps then
      pure ()
    else do

      -- add edges for matched args
      let matches i []     = pure ()
          matches i (p:ps) = do
            liftTCM (properlyMatching (namedThing $ unArg p)) >>= \case
              True  -> do topDef <- asks topDef
                          underPathOcc Matched Mixed $ addEdge (ArgNode topDef i)
              False -> pure ()
            matches (i + 1) ps
      matches 0 ps

      -- collect top def args from clause patterns
      let collectArgs :: Int -> NAPs -> [DefArgInEnv] -> [DefArgInEnv]
          collectArgs i []     acc = acc
          collectArgs i (p:ps) acc =
            let acc' = foldl' (\acc _ -> DefArgInEnv i [] : acc) acc
                              (namedThing $ unArg p)
            in collectArgs (i + 1) ps acc'

      local (\env -> env {topDefArgs = collectArgs 0 ps []}) do
        occurrences $ clauseBody cl

instance ComputeOccurrences Level where
  occurrences (Max _ as) = occurrences as

instance ComputeOccurrences PlusLevel where
  occurrences (Plus _ l) = occurrences l

instance ComputeOccurrences Type where
  occurrences (El _ v) = occurrences v

instance ComputeOccurrences a => ComputeOccurrences (Tele a) where
  occurrences EmptyTel        = mempty
  occurrences (ExtendTel a b) = occurrences a >> occurrences b

instance ComputeOccurrences a => ComputeOccurrences (Abs a) where
  {-# INLINE occurrences #-}
  occurrences = \case
    Abs _ t   -> underBinder $ occurrences t
    NoAbs _ t -> occurrences t

instance ComputeOccurrences a => ComputeOccurrences (Elim' a) where
  occurrences = \case
    Proj{}       -> __IMPOSSIBLE__
    Apply a      -> occurrences a
    IApply x y a -> occurrences x >> occurrences y >> occurrences a -- TODO Andrea: conservative

instance (ComputeOccurrences x, ComputeOccurrences a) => ComputeOccurrences (Boundary' x a) where
  occurrences = occurrences . theBoundary

instance ComputeOccurrences a => ComputeOccurrences [a] where
  occurrences = \case
    []   -> pure ()
    a:as -> occurrences a >> occurrences as

instance ComputeOccurrences a => ComputeOccurrences (Arg a)
instance ComputeOccurrences a => ComputeOccurrences (Dom a)
instance ComputeOccurrences a => ComputeOccurrences (Maybe a)

instance (ComputeOccurrences a, ComputeOccurrences b) => ComputeOccurrences (a, b) where
  {-# INLINE occurrences #-}
  occurrences (x, y) = occurrences x >> occurrences y

-- inConcreteOrAbstractMode :: QName -> (Definition -> OccM a) -> OccM a
-- inConcreteOrAbstractMode q k =

-- instance ComputeOccurrences Int where
--   occurrences _ = pure ()

-- -- | Compute occurrences in a given definition.
-- computeDefOccurences :: QName -> OccM ()
-- computeDefOccurences q = do
--   def <- lift $ lift $ ignoreAbstractMode $ getConstInfo q


-- buildOccurrenceGraph :: Set QName -> TCM (Graph Node Edge)
-- buildOccurrenceGraph qs = do

--   let go :: [QName] -> OccM ()
--       go qs = forM_ qs \q -> _

--   map <- runReaderT






















--------------------------------------------------------------------------------
