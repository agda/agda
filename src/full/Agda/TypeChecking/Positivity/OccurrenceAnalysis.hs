{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}
{-# OPTIONS_GHC -fmax-worker-args=20 #-}

#if __GLASGOW_HASKELL__ > 902
{-# OPTIONS_GHC -fworker-wrapper-cbv #-}
#endif

module Agda.TypeChecking.Positivity.OccurrenceAnalysis (
    Node
  , pattern DefNode
  , pattern ArgNode
  , Edge(..)
  , type OccGraph
  , type InvMutuals
  , buildOccurrenceGraph
  , stronglyConnComp
  , transitiveOccurrence
  , adjacencyList
  , lookupNode
  , toGenericGraph
  , fromGenericGraph
  , mutualIxToName
  ) where

import Prelude hiding ( null, (!!) )

import Data.Coerce
import Data.Foldable (foldl')
import Data.Hashable
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq, pattern (:|>))
import Data.Sequence qualified as DS
import Data.Graph qualified
import Data.Word
import Data.Bits
import Control.Exception
import System.IO.Unsafe

import Agda.Interaction.Options.Base (optOccurrence, optPolarity)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position (HasRange(..), noRange, Range)
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Monad hiding (getOccurrencesFromType)
import Agda.TypeChecking.Patterns.Match (properlyMatching)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Positivity.Warnings qualified as W
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Utils.ExpandCase
import Agda.Utils.Hash
import Agda.Utils.HashTable qualified as HT
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.SemiRing
import Agda.Utils.Size
import Agda.Utils.StrictReader
import Agda.Utils.Graph.AdjacencyMap.Unidirectional qualified as Graph
import Agda.Utils.MinimalArray.MutableLifted qualified as MArr
import Agda.Utils.MinimalArray.Lifted qualified as Arr


-- Graph nodes
----------------------------------------------------------------------------------------------------

-- Bit-packed representation of
-- data Node = DefNode Word32 | ArgNode Word32 Word31

newtype Node = Node Word64 deriving (Eq, Ord)

instance Hashable Node where
  hashWithSalt h (Node w) = fromIntegral (fromIntegral h `combineWord` fromIntegral w)

unpackNode# :: Word64 -> Either Int (Int, Int)
unpackNode# x
  | x .&. 1 == 0 = Left (fromIntegral (unsafeShiftR x 32))
  | otherwise    = Right (fromIntegral (unsafeShiftR x 32), fromIntegral (unsafeShiftR x 1 .&. 0xFFFFFFFF))

pattern DefNode :: Int -> Node
pattern DefNode x <- Node (unpackNode# -> Left x) where
  DefNode x = Node (fromIntegral (unsafeShiftL x 32))
{-# INLINE DefNode #-}

pattern ArgNode :: Int -> Int -> Node
pattern ArgNode x y <- Node (unpackNode# -> Right (x, y)) where
  ArgNode x y = Node (fromIntegral (unsafeShiftL x 32 .|. (unsafeShiftL y 1 + 1)))
{-# INLINE ArgNode #-}
{-# COMPLETE DefNode, ArgNode #-}

instance Show Node where
  showsPrec p (DefNode x)   =
    showParen (p > 10) (("DefNode " ++) . showsPrec (p + 1) x)
  showsPrec p (ArgNode x y) =
    showParen (p > 10) (("ArgNode " ++) . showsPrec (p + 1) x . (' ':) . showsPrec (p + 1) y)

instance P.Pretty Node where
  pretty = \case
    DefNode q   -> P.pretty q
    ArgNode q i -> P.pretty q <> P.text ("." ++ show i)

-- Maps keyed by Node
----------------------------------------------------------------------------------------------------

type NodeMap v = HT.HashTableUL Word64 v

-- Getting the "found" and "not found" branches as arguments
{-# INLINE lookupNode #-}
lookupNode :: Node -> NodeMap v -> (v -> IO a) -> IO a -> IO a
lookupNode (Node n) map found notfound = HT.lookupCPS n map found notfound

{-# NOINLINE insertNode #-}
insertNode :: Node -> v -> NodeMap v -> IO ()
insertNode (Node n) v map = HT.insert map n v

{-# NOINLINE nodeMapToList #-}
nodeMapToList :: NodeMap v -> IO [(Node, v)]
nodeMapToList map = coerce (HT.toList map)

{-# NOINLINE cloneNodeMap #-}
cloneNodeMap :: NodeMap v -> IO (NodeMap v)
cloneNodeMap = HT.clone

-- Labeling mutual QName-s with consecutive Int-s
----------------------------------------------------------------------------------------------------

type Mutuals    = HT.HashTableLU QName Int
type InvMutuals = Arr.Array QName

-- Getting the "found" and "not found" branches as arguments
{-# INLINE lookupMutual #-}
lookupMutual :: QName -> (Int -> OccM a) -> OccM a -> OccM a
lookupMutual q found notfound = ReaderT \oenv -> TCM \tcs tce ->
  HT.lookupCPS q (mutuals oenv)
    (\i -> unTCM (runReaderT (found i) oenv) tcs tce)
    (unTCM (runReaderT notfound oenv) tcs tce)

{-# NOINLINE insertMutual #-}
insertMutual :: QName -> Int -> Mutuals -> IO ()
insertMutual q i muts = HT.insert muts q i

invertMutuals :: Mutuals -> IO InvMutuals
invertMutuals muts = do
  size <- HT.size muts
  arr <- MArr.new size undefined
  HT.forAssocs muts \q i -> MArr.write arr i q
  MArr.unsafeFreeze arr

mutualIxToName :: InvMutuals -> Int -> QName
mutualIxToName = Arr.index

-- Occurrence graph
----------------------------------------------------------------------------------------------------

-- | Meaning of the graph: the keys in the outer NodeMap occur in the keys of the inner NodeMap.
type OccGraph = NodeMap (NodeMap (Edge OccursWhere))

{-# NOINLINE addEdgeToGraph #-}
addEdgeToGraph :: Node -> Node -> Edge OccursWhere -> OccGraph -> IO ()
addEdgeToGraph src tgt e graph = lookupNode src graph
  (\tgts -> lookupNode tgt tgts
    (\e' -> insertNode tgt (mergeEdges e e') tgts)
    (insertNode tgt e tgts))
  (do
    tgts <- HT.empty
    insertNode tgt e tgts
    insertNode src tgts graph)

{-# NOINLINE adjacencyList #-}
adjacencyList :: OccGraph -> IO [(Node, Node, Edge OccursWhere)]
adjacencyList graph = do
  assocs <- nodeMapToList graph
  assocs <- forM assocs \(src, tgts) -> (src,) <$!> nodeMapToList tgts
  pure [(src, tgt, e) | (src, tgts) <- assocs, (tgt, e) <- tgts]

{-# NOINLINE addTargetNodesAsSource #-}
-- | For every node appearing as a target but not as a source, add it as a source node with empty
--   map for targets. This is an invariant that's required by Data.Graph.stronglyConnComp.
addTargetNodesAsSource :: OccGraph -> IO OccGraph
addTargetNodesAsSource graph = do
  graph' <- cloneNodeMap graph
  HT.forAssocs graph \(Node -> src) tgts ->
    HT.forAssocs tgts \(Node -> tgt) _ -> lookupNode tgt graph
      (\_ -> pure ())
      (do
        edges <- HT.empty
        insertNode tgt edges graph')
  pure graph'

{-# NOINLINE stronglyConnComp #-}
-- | Strongly connected components, in reverse topological order.
stronglyConnComp :: OccGraph -> IO [Data.Graph.SCC Node]
stronglyConnComp graph = do
  graph  <- addTargetNodesAsSource graph
  assocs <- nodeMapToList graph
  assocs <- forM assocs \(src, tgts) -> (src,src,) . map fst <$!> nodeMapToList tgts
  pure $! Data.Graph.stronglyConnComp assocs

{-# NOINLINE toGenericGraph #-}
-- | Convert to generic Utils graph, for the purpose of testing and warning rendering.
toGenericGraph :: (OccGraph, InvMutuals) -> Graph.Graph Node (Edge W.OccursWhere)
toGenericGraph (!graph, !muts) = unsafeDupablePerformIO do

  let convEdge :: Edge OccursWhere -> IO (Edge W.OccursWhere)
      convEdge (Edge occ (OccursWhere rng path)) = Edge occ <$!> convPath rng path

      convPath :: Range -> OccursPath -> IO W.OccursWhere
      convPath rng path = let

        go' :: OccursPath -> IO (Seq W.Where)
        go' = \case
          Root            -> pure mempty
          MutDefArg p x i -> do x <- pure $ mutualIxToName muts x
                                (:|> W.DefArg x i) <$!> go' p
          LeftOfArrow p   -> (:|> W.LeftOfArrow)   <$!> go' p
          DefArg p x i    -> (:|> W.DefArg x i)    <$!> go' p
          UnderInf p      -> (:|> W.UnderInf)      <$!> go' p
          VarArg p i o    -> (:|> W.VarArg o i)    <$!> go' p
          MetaArg p       -> (:|> W.MetaArg)       <$!> go' p
          ConArgType p x  -> (:|> W.ConArgType x)  <$!> go' p
          IndArgType p x  -> (:|> W.IndArgType x)  <$!> go' p
          ConEndpoint p x -> (:|> W.ConEndpoint x) <$!> go' p
          InClause p i    -> (:|> W.InClause i)    <$!> go' p
          Matched p       -> (:|> W.Matched)       <$!> go' p
          InIndex p       -> (:|> W.InIndex)       <$!> go' p
          InDefOf p x     -> (:|> W.InDefOf x)     <$!> go' p

        go :: OccursPath -> IO (Seq W.Where, Seq W.Where)
        go = \case
          Root            -> pure (mempty, mempty)
          MutDefArg p x i -> do x <- pure $ mutualIxToName muts x
                                s1 <- go' p
                                let s2 = DS.singleton (W.DefArg x i)
                                pure (s1, s2)
          LeftOfArrow p   -> ((:|> W.LeftOfArrow)   <$!>) <$!> go p
          DefArg p x i    -> ((:|> W.DefArg x i)    <$!>) <$!> go p
          UnderInf p      -> ((:|> W.UnderInf)      <$!>) <$!> go p
          VarArg p i o    -> ((:|> W.VarArg o i)    <$!>) <$!> go p
          MetaArg p       -> ((:|> W.MetaArg)       <$!>) <$!> go p
          ConArgType p x  -> ((:|> W.ConArgType x)  <$!>) <$!> go p
          IndArgType p x  -> ((:|> W.IndArgType x)  <$!>) <$!> go p
          ConEndpoint p x -> ((:|> W.ConEndpoint x) <$!>) <$!> go p
          InClause p i    -> ((:|> W.InClause i)    <$!>) <$!> go p
          Matched p       -> ((:|> W.Matched)       <$!>) <$!> go p
          InIndex p       -> ((:|> W.InIndex)       <$!>) <$!> go p
          InDefOf p x     -> ((:|> W.InDefOf x)     <$!>) <$!> go p

        in do (s1, s2) <- go path
              pure $ W.OccursWhere rng s1 s2

  let go :: [(Node, Node, Edge OccursWhere)]
         -> Map Node (Map Node (Edge W.OccursWhere))
         -> IO (Map Node (Map Node (Edge W.OccursWhere)))
      go ((src, tgt, e):rest) m = do
        e <- convEdge e
        let m' =  Map.insertWith (\_ -> Map.insert tgt e) src (Map.singleton tgt e)
                $ Map.insertWith (\_ tgts -> tgts) tgt mempty
                $ m
        go rest m'
      go [] m = pure m

  assocs <- adjacencyList graph
  Graph.Graph <$!> go assocs mempty

-- | Make a graph from a generic one. We use this in testing in Internal.TypeChecking.Positivity
--   where it's much more convenient to generate immutable graphs. Note: we ignore occurrence
--   location info.
{-# NOINLINE fromGenericGraph #-}
fromGenericGraph :: Graph.Graph Node (Edge a) -> OccGraph
fromGenericGraph (Graph.Graph graph) = unsafeDupablePerformIO do
  graph' <- HT.empty
  forM_ (Map.toList graph) \(src, tgts) ->
    forM_ (Map.toList tgts) \(tgt, Edge o _) ->
      addEdgeToGraph src tgt (Edge o (OccursWhere noRange Root)) graph'
  pure graph'


-- Occurrence analysis
----------------------------------------------------------------------------------------------------

{-
Occurrence analysis is a single traversal over definitions which builds a mutable graph in IO.
We keep track of the "path" during traversal that leads from the current position to a top
definition. If positivity checking produces warnings, the paths get processed into those warnings.
-}

-- | Top-level arg index that a local variable was bound in, arg polarity of the var itself.
data DefArgInEnv = DefArgInEnv Int [Occurrence]
  deriving Show

data OccEnv = OccEnv {
    topDef     :: Int           -- ^ The definition we're working under (as n-th definition in the mutual block)
  , topDefArgs :: [DefArgInEnv] -- ^ Occurrence info for definition args.
  , inf        :: Maybe QName   -- ^ Name for ∞ builtin.
  , locals     :: Int           -- ^ Number of local binders (on the top of the definition args).
  , mutuals    :: Mutuals       -- ^ Int labeling of definition names in the current mutual group.
  , target     :: Node          -- ^ We add occurrences pointing to this node.
  , path       :: OccursPath    -- ^ Path from the target node to the current position.
  , occ        :: Occurrence    -- ^ Occurence of current position.
  , graph      :: OccGraph      -- ^ Graph that's being built.
  }

type OccM = ReaderT OccEnv TCM

instance PrettyTCMWithNode (Edge OccursWhere) where
  prettyTCMWithNode (WithNode n (Edge o (OccursWhere _ w))) = vcat
    [ prettyTCM o <+> prettyTCM n
    , nest 2 $ return $ P.pretty w
    ]

{-# INLINE underPath #-}
underPath :: (OccursPath -> OccursPath) -> OccM a -> OccM a
underPath f = local \env -> env {path = f (path env)}

{-# INLINE underOcc #-}
underOcc :: Occurrence -> OccM a -> OccM a
underOcc p = local \env -> env {occ = otimes (occ env) p}

{-# INLINE underBinder #-}
underBinder :: OccM a -> OccM a
underBinder = local \env -> env {locals = locals env + 1}

{-# INLINE underPathOcc #-}
-- | Modify the current path and 'otimes' a new 'Occurrence' to the
--   current occurrence.
underPathOcc :: (OccursPath -> OccursPath) -> Occurrence -> OccM a -> OccM a
underPathOcc f p = local \e -> e {path = f (path e), occ = otimes (occ e) p}

{-# INLINE underPathSetOcc #-}
-- | Modify the current path and set the current 'Occurence' to
--   the given value.
underPathSetOcc :: (OccursPath -> OccursPath) -> Occurrence -> OccM a -> OccM a
underPathSetOcc f p = local \e -> e {path = f (path e), occ = p}

getOccurrencesFromType :: Type -> TCM [Occurrence]
getOccurrencesFromType a = (optPolarity <$> pragmaOptions) >>= \case
  False -> pure []
  True  -> do
    let go :: Type -> ReduceM [Occurrence]
        go a = (unEl <$> reduce a) >>= \case
          Pi a b -> do
            let p = modalPolarityToOccurrence $ modPolarityAnn $ getModalPolarity a
            ~ps <- underAbsReduceM a b \b -> go b
            pure (p:ps)
          _ -> pure []
    liftReduce (go a)

addEdge :: Range -> Node -> OccM ()
addEdge rng src = do
  target <- asks target
  path   <- asks path
  occ    <- asks occ
  graph  <- asks graph
  expand \ret -> case occ of
    Unused -> ret $ pure ()
    occ    -> ret do
      let e = Edge occ (OccursWhere rng path)
      lift $ lift $ addEdgeToGraph src target e graph

-- | Recurse into an argument of a non-mutual definition.
occurrencesInDefArg :: QName -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArg d p i e = expand \ret -> case p of
  Unused -> ret $ pure ()
  p      -> ret $ underPathOcc (\p -> DefArg p d i) p $ occurrences e

-- | Recurse into an argument of an argument of the top definition.
occurrencesInDefArgArg :: Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArgArg p i e = expand \ret -> case p of
  Unused -> ret $ pure ()
  p      -> ret $ underPathOcc (\x -> VarArg x i p) p $ occurrences e

-- | Recurse into an argument of a mutual definition.
occurrencesInMutDefArg :: Int -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInMutDefArg di p i e = expand \ret -> case p of
  Unused -> ret $ pure ()
  p      -> ret $ local (\e -> e {path = MutDefArg (path e) di i, target = ArgNode di i, occ = p}) $
                    occurrences e

mutualDefOcc :: Definition -> Occurrence
mutualDefOcc d = case theDef d of
  Datatype{} -> GuardPos
  _          -> StrictPos

class ComputeOccurrences a where
  occurrences :: a -> OccM ()

  {-# INLINE occurrences #-}
  default occurrences :: (Foldable t, ComputeOccurrences b, a ~ t b) => a -> OccM ()
  occurrences = mapM_ occurrences

instance ComputeOccurrences Term where
  occurrences t = expand \ret -> case unSpine t of

    Var x es -> ret do
      locals <- asks locals

      -- it's a locally bound variable, all args are Mixed occurrence,
      -- we don't record an occurrence for the variable
      if x < locals then do
        let elims i es = expand \ret -> case es of
              []   -> ret $ pure ()
              e:es -> ret $ underPath (\p -> VarArg p i Mixed) (occurrences e) >> elims (i + 1) es

        underOcc Mixed $ elims 0 es

      -- it's bound in a top-level definition argument
      else do
        let elims i ps es = expand \ret -> case (ps, es) of
              (_   , []  ) -> ret $ pure ()
              ([]  , e:es) -> ret $ occurrencesInDefArgArg Mixed i e >> elims (i + 1) [] es
              (p:ps, e:es) -> ret $ occurrencesInDefArgArg p i e     >> elims (i + 1) ps es
        topDefArgs <- asks topDefArgs
        topDef     <- asks topDef
        let DefArgInEnv argix ps = topDefArgs !! (x - locals)
        addEdge noRange (ArgNode topDef argix)
        elims 0 ps es

    Def d es -> ret $ asks inf >>= \case

      -- ∞ application
      Just inf | d == inf -> case es of
        []     -> pure ()
        [_]    -> pure () -- unused arg
        [_, e] -> underPathOcc UnderInf GuardPos $ occurrences e
        _      -> __IMPOSSIBLE__

      _ -> lookupMutual d

        -- it's a mutual definition
        (\di -> do
          addEdge (getRange d) (DefNode di)
          expand \ret -> case es of
            [] -> ret $ pure ()  -- we skip the mutualDefOcc in this case
            es -> ret do
              let elims di p i es = expand \ret -> case es of
                    []   -> ret $ pure ()
                    e:es -> ret do occurrencesInMutDefArg di p i e
                                   elims di p (i + 1) es

              defOcc <- lift (mutualDefOcc <$> getConstInfo d)
              elims di defOcc 0 es
        )

        -- not a mutual definition
        (do
          def <- lift $ getConstInfo d
          case theDef def of
            Constructor{} -> do
              let elims i es = expand \ret -> case es of
                    []   -> ret $ pure ()
                    e:es -> ret do occurrencesInDefArg d StrictPos i e
                                   elims (i + 1) es
              elims 0 es

            _ -> do
              let elims' :: QName -> Int -> [Occurrence] -> Elims -> OccM ()
                  elims' d i ps es = expand \ret -> case (ps, es) of
                    (_   , []  ) -> ret $ pure ()
                    (p:ps, e:es) -> ret do occurrencesInDefArg d p i e
                                           elims' d (i + 1) ps es
                    ([],   e:es) -> ret do occurrencesInDefArg d Mixed i e
                                           elims' d (i + 1) ps es

              let elims :: QName -> Type -> Int -> [Occurrence] -> Elims -> OccM ()
                  elims d a i ps es = expand \ret -> case (ps, es) of
                    (_   , []  ) -> ret $ pure ()
                    (p:ps, e:es) -> ret do occurrencesInDefArg d p i e
                                           elims d a (i + 1) ps es
                    ([]  , e:es) -> ret do ps <- lift $ getOccurrencesFromType a
                                           elims' d i (drop i ps) (e:es)

              let defOcc = mutualDefOcc def
              let argOccs = defArgOccurrences def
              underOcc defOcc $ elims d (defType def) 0 argOccs es
         )

    Con _ _ es -> ret $ occurrences es
    MetaV m es -> ret $ underPathSetOcc MetaArg Mixed (occurrences es)
    Pi a b     -> ret $ underPathOcc LeftOfArrow JustNeg (occurrences a) >> occurrences b
    Lam _ t    -> ret $ occurrences t
    Level l    -> ret $ occurrences l
    Lit{}      -> ret $ pure ()
    Sort{}     -> ret $ pure ()
    -- Jesper, 2020-01-12: this information is also used for the
    -- occurs check, so we need to look under DontCare (see #4371)
    DontCare t -> ret $ occurrences t
    Dummy{}    -> ret $ pure ()

-- | Record that every matched argument of a def occurs in the def.
addClauseArgMatches :: NAPs -> OccM ()
addClauseArgMatches ps = underPathSetOcc Matched Mixed $ go 0 ps where
  go :: Int -> NAPs -> OccM ()
  go i ps = expand \ret -> case ps of
    []   -> ret $ pure ()
    p:ps -> ret do
      lift (properlyMatching (namedThing $ unArg p)) >>= \case
        True  -> do topDef <- asks topDef
                    addEdge noRange (ArgNode topDef i)
        False -> pure ()
      go (i + 1) ps

instance ComputeOccurrences Clause where
  occurrences cl = do
    let ps = namedClausePats cl
    -- TODO #3733: handle hcomp/transp clauses properly
    if hasDefP ps then
      pure ()
    else do
      -- add edges for matched args
      addClauseArgMatches ps

      let collectArgs :: NAPs -> [DefArgInEnv]
          collectArgs ps = IntMap.elems $ go 0 ps mempty where
            go :: Int -> NAPs -> IntMap DefArgInEnv -> IntMap DefArgInEnv
            go i []     acc = acc
            go i (p:ps) acc =
              -- TODO: we get crappy GHC Core for Pattern' foldl'
              let acc' = foldl'
                          (\acc j -> IntMap.insert (dbPatVarIndex j) (DefArgInEnv i []) acc)
                          acc (namedThing $ unArg p)
              in go (i + 1) ps acc'

      let items = collectArgs ps
      -- process body
      local (\env -> env {topDefArgs = items}) do
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

-- András 2026-02-18: CAUTION. Make sure to only use this instance if
-- there's no Path or Occurrence to be adjusted.
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

instance ComputeOccurrences Int where
  {-# INLINE occurrences #-}
  occurrences _ = pure ()

-- | Compute occurrences in a given definition.
computeDefOccurrences :: QName -> Int -> OccM ()
computeDefOccurrences q qi = inConcreteOrAbstractMode q \def -> do
  reportSDoc "tc.pos" 25 do
    let a = defAbstract def
    m   <- asksTC envAbstractMode
    cur <- asksTC envCurrentModule
    o   <- asksTC envCurrentOpaqueId
    "computeOccurrences" <+> prettyTCM q <+> text (show a) <+> text (show o) <+> text (show m)
      <+> prettyTCM cur

  let paramsToDefArgs :: Telescope -> TCM [DefArgInEnv]
      paramsToDefArgs tel = go 0 (telToList tel) [] where
        go i as acc = expand \ret -> case as of
          []   -> ret $ pure acc
          a:as -> ret do occs <- getOccurrencesFromType (snd (unDom a))
                         go (i + 1) as (DefArgInEnv i occs : acc)

  let defOcc = mutualDefOcc def
  underPathOcc (`InDefOf` q) defOcc $ expand \ret -> case theDef def of

    Function{funClauses = cs} -> ret do

      cs <- lift $ mapM etaExpandClause =<< instantiateFull cs
      performAnalysis <- lift $ optOccurrence <$> pragmaOptions
      if performAnalysis then do
        let clauses i cs = expand \ret -> case cs of
              []   -> ret $ pure ()
              c:cs -> ret $ underPath (`InClause` i) (occurrences c) >> clauses (i + 1) cs
        clauses 0 cs
      else case cs of
        []   -> __IMPOSSIBLE__

        -- András 2026-02-18: this looks dodgy?
        cl:_ -> underPathSetOcc Matched Mixed do
          let go i ps = expand \ret -> case ps of
                []   -> ret $ pure ()
                _:ps -> ret do d <- asks topDef
                               addEdge noRange (ArgNode qi i)
                               go (i + 1) ps
          go 0 (namedClausePats cl)

    Datatype{dataClause = Just c} -> ret $ occurrences =<< lift (instantiateFull c)

    Datatype{dataPars = np0, dataCons = cs, dataTranspIx = trx} -> ret do
      -- Andreas, 2013-02-27 (later edited by someone else): First,
      -- include each index of an inductive family.
      TelV telD _ <- lift $ telView $ defType def
      -- Andreas, 2017-04-26, issue #2554: count first index as parameter if it has type Size.
      -- We compute sizeIndex=1 if first first index has type Size, otherwise sizeIndex==0
      sizeIndex <- lift $ caseList (drop np0 $ telToList telD) (pure 0) \dom _ ->
                          caseMaybeM (isSizeType dom) (pure 0) \_ ->
                          pure 1

      let np = np0 + sizeIndex -- number of parameters

      -- add edge for size index, if it exists
      expand \ret -> case sizeIndex of
        1 -> ret $ addEdge noRange (ArgNode qi np0)
        _ -> ret $ pure ()

      -- add edges for indices
      underPathSetOcc InIndex Mixed $
        rangeM_ np (size telD - 1) \i -> addEdge noRange (ArgNode qi i)


      -- Then, we compute the occurrences in the constructor types.
      --------------------------------------------------------------------------------

      -- If the data type has a transport constructor (i.e. it's an
      -- indexed family in cubical mode) we should also consider it for
      -- positivity.
      cs <- maybe (pure cs) (\c -> pure (cs ++ [c])) trx
      forM_ cs \c -> do
         -- Andreas, 2020-02-15, issue #4447:
         -- Allow UnconfimedReductions here to make sure we get the constructor type
         -- in same way as it was obtained when the data types was checked.
        (TelV tel t, bnd) <- lift $ putAllowedReductions allReductions $
                                    telViewPathBoundary . defType =<< getConstInfo c
        let (tel0,tel1) = splitTelescopeAt np tel
        -- Do not collect occurrences in the data parameters.
        -- Normalization needed e.g. for test/succeed/Bush.agda.
        -- (Actually, for Bush.agda, reducing the parameters should be sufficient.)
        tel1' <- lift $ addContext tel0 $ normalise tel1 -- András 2026-02-18: why addContext?
        pvars <- lift $ paramsToDefArgs tel0

        local (\env -> env {topDefArgs = pvars}) do
          -- edges in the types of constructor arguments
          underPath (`ConArgType` c) $ occurrences tel1'

          local (\env -> env {locals = size tel - np}) do

            -- edges in path boundary
            underPath (`ConEndpoint` c) $ occurrences bnd

            -- Occurrences in the indices of the data type the constructor targets.
            -- Andreas, 2020-02-15, issue #4447:
            -- WAS: @t@ is not necessarily a data type, but it could be something
            -- that reduces to a data type once UnconfirmedReductions are confirmed
            -- as safe by the termination checker.
            -- In any case, if @t@ is not showing itself as the data type, we need to
            -- do something conservative.  We will just collect *all* occurrences
            -- and flip their sign (variance) using 'LeftOfArrow'.
            case unEl t of
              Def q' vs
                | q == q' -> do
                    let indices = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ drop np vs
                    underPathSetOcc (`IndArgType` c) Mixed $ occurrences indices
                | otherwise -> __IMPOSSIBLE__  -- this ought to be impossible now (but wasn't, see #4447)
              Pi{}       -> __IMPOSSIBLE__  -- eliminated  by telView
              MetaV{}    -> __IMPOSSIBLE__  -- not a constructor target; should have been solved by now
              Var{}      -> __IMPOSSIBLE__  -- not a constructor target
              Sort{}     -> __IMPOSSIBLE__  -- not a constructor target
              Lam{}      -> __IMPOSSIBLE__  -- not a type
              Lit{}      -> __IMPOSSIBLE__  -- not a type
              Con{}      -> __IMPOSSIBLE__  -- not a type
              Level{}    -> __IMPOSSIBLE__  -- not a type
              DontCare{} -> __IMPOSSIBLE__  -- not a type
              Dummy{}    -> __IMPOSSIBLE__

    Record{recClause = Just c} -> ret do
      occurrences =<< lift (instantiateFull c)

    Record{recPars = np, recTel = tel} -> ret do
      let (tel0, tel1) = splitTelescopeAt np tel
      pvars <- lift $ paramsToDefArgs tel0
      local (\env -> env {topDefArgs = pvars}) do
        occurrences =<< liftTCM (addContext tel0 (normalise tel1))
        -- Andreas, 2017-01-01, issue #1899, treat like data types

    -- Arguments to other kinds of definitions are hard-wired.
    Constructor{}      -> ret mempty
    Axiom{}            -> ret mempty
    DataOrRecSig{}     -> ret mempty
    Primitive{}        -> ret mempty
    PrimitiveSort{}    -> ret mempty
    GeneralizableVar{} -> ret mempty
    AbstractDefn{}     -> ret __IMPOSSIBLE__

buildOccurrenceGraph :: [QName] -> TCM (OccGraph, InvMutuals)
buildOccurrenceGraph qs = do
  inf     <- maybe Nothing (\x -> Just $! nameOfInf x) <$> coinductionKit
  graph   <- lift HT.empty
  mutuals <- lift HT.empty

  TCM \_ _ -> do
    let init []     i = pure ()
        init (q:qs) i = insertMutual q i mutuals >> init qs (i + 1)
    init qs 0

  TCM \st tce -> HT.forAssocs mutuals \q i -> do
    let env = OccEnv i [] inf 0 mutuals (DefNode i) Root StrictPos graph
    unTCM (runReaderT (computeDefOccurrences q i) env) st tce

  mutuals <- lift $ invertMutuals mutuals
  pure (graph, mutuals)


-- Computing transitive occurrences, to be used in positivity checking
----------------------------------------------------------------------------------------------------

data Seen = Seen Node Occurrence
  deriving (Eq, Show)

instance Hashable Seen where
  hashWithSalt h (Seen x y) =
    fromIntegral (fromIntegral (hashWithSalt h x) `combineWord` fromIntegral (fromEnum y))

-- | Set of visited nodes during graph search.
type SeenNodes = HT.HashTableLL Seen ()

memberSeen :: Seen -> SeenNodes -> IO Bool
memberSeen x map = HT.lookup map x >>= \case
  Nothing -> pure False
  _       -> pure True

{-# NOINLINE insertSeen #-}
insertSeen :: Seen -> SeenNodes -> IO ()
insertSeen x map = HT.insert map x ()

-- | Exception for short-circuiting when finding a Mixed path from source to target.
instance Exception Occurrence

-- | Search for transitive occurrences through the occurrence graph. We compute the 'oplus' sum of
--   all paths from the source to the target. This is not as bad as it sounds, becuse a) we can
--   short-circuit a search when a 'Mixed' path is found b) only 4 possible 'Occurrences' remain,
--   (discounting 'Mixed' and 'Unused') and we can use a DFS where each node is visited at most 4
--   times, for each 'Occurence' of the path to the node from the source.
transitiveOccurrence :: OccGraph -> Node -> Node -> IO Occurrence
transitiveOccurrence graph src tgt = do

      -- Function for visiting a node.
  let go :: OccGraph -> Node -> Node -> Occurrence -> Occurrence -> SeenNodes -> IO Occurrence
      go graph tgt src path acc seen = do
        let s = Seen src path
        memberSeen s seen >>= \case
          True  -> pure acc
          False -> do
            insertSeen s seen
            if src == tgt then
              case oplus path acc of
                Mixed -> throwIO Mixed  -- Mixed path found, abort search
                acc   -> go' graph tgt src path acc seen
            else
              go' graph tgt src path acc seen

      -- Function for visiting the children of a node
      go' :: OccGraph -> Node -> Node -> Occurrence -> Occurrence -> SeenNodes -> IO Occurrence
      go' graph tgt src path acc seen = lookupNode src graph
        (\map -> lookupNode tgt map
          -- if there's a direct edge to the target, we follow that first.
          -- this should make it faster to find Mixed edges (if there's one)
          (\(Edge occ _) -> do
            acc <- go graph tgt tgt (otimes path occ) acc seen
            goMap graph tgt map path acc seen)

          (goMap graph tgt map path acc seen))

        (pure acc)

      -- Function for traversing the map of children for a node
      goMap :: OccGraph -> Node -> NodeMap (Edge OccursWhere) -> Occurrence -> Occurrence -> SeenNodes -> IO Occurrence
      goMap graph tgt map path acc seen =
        HT.forAssocsAccum map acc \(Node -> src) (Edge occ _) acc ->
          if src == tgt then pure acc -- already covered this case in go'
                        else go graph tgt src (otimes path occ) acc seen

  seen <- HT.empty
  go' graph tgt src StrictPos Unused seen `catch` pure
