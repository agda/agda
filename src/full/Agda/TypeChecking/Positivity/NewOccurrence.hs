{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}
{-# OPTIONS_GHC -fmax-worker-args=20 #-}
{-# OPTIONS_GHC -fmax-valid-hole-fits=0 -fmax-relevant-binds=3 #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -dno-typeable-binds -ddump-to-file #-}

#if __GLASGOW_HASKELL__ > 902
{-# OPTIONS_GHC -fworker-wrapper-cbv #-}
#endif

module Agda.TypeChecking.Positivity.NewOccurrence where

import Prelude hiding ( null, (!!) )

-- import Data.Foldable
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Interaction.Options.Base (optOccurrence, optPolarity)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.TypeChecking.Datatypes (isDataOrRecordType)
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Monad hiding (getOccurrencesFromType)
import Agda.TypeChecking.Patterns.Match (properlyMatching)
import Agda.TypeChecking.Positivity.Occurrence (Occurrence(..), modalPolarityToOccurrence)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Map qualified as Map
import Agda.Utils.Maybe
import Agda.Utils.SemiRing
import Agda.Utils.Size
import Agda.Utils.Monad
import Agda.Utils.StrictReader
import Agda.Utils.StrictState
import Agda.Utils.ExpandCase

--------------------------------------------------------------------------------
{-
TODO:
- TRANSPOSE graph + use bfs!
- purge telView-s if possible
- mutable hashtable Graph

NOTE:
- We can't avoid recursing into Unused args becuse we might
  have metavars there, which have constant Mixed arg polarity
  and must be traversed in all cases!
  Proposal: change behavior, skip all Unused subterms

Possible issues in old impl:
- lack of Path/Occ handling in record constructors?

- In no-occurrence-analysis mode we only look at the first clause of functions to
  match the args

- computeDefOccurrences tel1' : why addContext?

- The graph library requires that every target of an edge appears as a source node.

- We don't record unused edges in the graph.
  The Unused value only appears when we set occurrences in the signature.
  Imprecise representation in occ analysis.

- The eta expansion of clause bodies does a "raise n", which is Not Good

-}


--------------------------------------------------------------------------------

data Path
  = Root
  | LeftOfArrow Path
  | DefArg Path QName Nat         -- ^ in the nth argument of a defined constant
  | MutDefArg Path QName Nat      -- ^ in the nth argument of a def in the current mutual block
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
  deriving Eq

instance Show Path where
  show p = go p [] where
    go p acc = case p of
      Root            -> acc
      LeftOfArrow p   -> go p $ " InLeftOfArrow" ++ acc
      DefArg p q i    -> go p $ " InDefArg "      ++ P.prettyShow q ++ " " ++ P.prettyShow i ++ acc
      MutDefArg p q i -> go p $ " InMutDefArg "   ++ P.prettyShow q ++ " " ++ P.prettyShow i ++ acc
      UnderInf p      -> go p $ " InUnderInf" ++ acc
      VarArg p i      -> go p $ " InVarArg "      ++ P.prettyShow i ++ acc
      MetaArg p       -> go p $ " InMetaArg" ++ acc
      ConArgType p q  -> go p $ " InConArgType "  ++ P.prettyShow q ++ acc
      IndArgType p q  -> go p $ " InIndArgType "  ++ P.prettyShow q ++ acc
      ConEndpoint p q -> go p $ " InConEndpoint " ++ P.prettyShow q ++ acc
      InClause p i    -> go p $ " InClause "    ++ P.prettyShow i ++ acc
      Matched p       -> go p $ " Matched" ++ acc
      IsIndex p       -> go p $ " IsIndex" ++ acc
      InDefOf p q     -> go p $ " InDefOf " ++ P.prettyShow q ++ acc

instance P.Pretty Path where
  pretty = P.text . show

instance PrettyTCM Path where
  prettyTCM = return . P.pretty

data Node = DefNode QName | ArgNode QName Nat
  deriving (Eq, Ord, Show)

instance P.Pretty Node where
  pretty = \case
    DefNode q   -> P.pretty q
    ArgNode q i -> P.pretty q <> P.text ("." ++ show i)

instance PrettyTCM Node where
  prettyTCM = return . P.pretty

-- | Top-level arg index that a local variable was bound in, arg polarity of the var itself.
data DefArgInEnv = DefArgInEnv Int [Occurrence]
  deriving Show

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

data Edge     = Edge Occurrence Path deriving (Eq, Show)
type OccGraph = Map Node (Map Node Edge)
type OccM     = ReaderT OccEnv (StateT OccGraph TCM)

instance PrettyTCMWithNode Edge where
  prettyTCMWithNode (WithNode n (Edge o w)) = vcat
    [ prettyTCM o <+> prettyTCM n
    , nest 2 $ return $ P.pretty w
    ]

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
-- | Modify the current path and 'otimes' a new 'Occurrence' to the
--   current occurrence.
underPathOcc :: (Path -> Path) -> Occurrence -> OccM a -> OccM a
underPathOcc f p = local \e -> e {path = f (path e), occ = otimes (occ e) p}

{-# INLINE underPathSetOcc #-}
-- | Modify the current path and set the current 'Occurence' to
--   the given value.
underPathSetOcc :: (Path -> Path) -> Occurrence -> OccM a -> OccM a
underPathSetOcc f p = local \e -> e {path = f (path e), occ = p}

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

addEdgeToGraph :: Node -> Node -> Edge -> OccGraph -> OccGraph
addEdgeToGraph src target e g =
  Map.insertWithGood
    (\(!e,!target) _ m -> Map.insertWithGood (\_ -> mergeEdges) () target e m)
    (e,target)
    src
    (Map.singleton target e)
    g

addEdge :: Node -> OccM ()
addEdge src = do
  target <- asks target
  path   <- asks path
  occ    <- asks occ
  expand \ret -> case occ of
    Unused -> ret $ pure ()
    occ    -> ret $ modify $ addEdgeToGraph src target (Edge occ path)

occurrencesInDefArg :: QName -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArg d p i e = expand \ret -> ret do
  underPathOcc (\p -> DefArg p d i) p $ occurrences e

occurrencesInDefArgArg :: Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArgArg p i e = expand \ret -> ret do
  underPathOcc (`VarArg` i) p $ occurrences e

occurrencesInMutDefArg :: QName -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInMutDefArg d p i e = expand \ret -> ret $
  local (\e -> e {path = MutDefArg (path e) d i, target = ArgNode d i, occ = p}) $
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

      tda <- asks topDefArgs
      -- reportSLn "" 1 $ "VAR " ++ P.prettyShow (Var x es) ++ " " ++ show (locals, tda)

      -- it's a locally bound variable, all args are Mixed occurrence,
      -- we don't record an occurrence for the variable
      if x < locals then do
        let elims i es = expand \ret -> case es of
              []   -> ret $ pure ()
              e:es -> ret $ underPath (`VarArg` i) (occurrences e) >> elims (i + 1) es

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
        addEdge (ArgNode topDef argix)
        elims 0 ps es

    Def d es -> asks inf >>= \case

      -- ∞ application
      Just inf | d == inf -> case es of
        []     -> pure ()
        [_]    -> pure () -- unused arg
        [_, e] -> underPathOcc UnderInf GuardPos $ occurrences e
        _      -> __IMPOSSIBLE__

      _ -> do
        mutuals <- asks mutuals
        def     <- liftTCM $ getConstInfo d

        -- it's a mutual definition
        if Set.member d mutuals then do
          addEdge (DefNode d)
          expand \ret -> case es of
            [] -> ret $ pure ()  -- we skip the mutualDefOcc in this case
            es -> ret do
              let elims d p i es = expand \ret -> case es of
                    []   -> ret $ pure ()
                    e:es -> ret do occurrencesInMutDefArg d p i e
                                   elims d p (i + 1) es

              defOcc <- liftTCM $ mutualDefOcc d
              elims d defOcc 0 es

        -- not a mutual definition
        else case theDef def of


          Constructor{} -> do
            -- reportSLn "" 1 $ "CONSTRUCTOR " ++ P.prettyShow d
            let elims i es = expand \ret -> case es of
                  []   -> ret $ pure ()
                  e:es -> ret do occurrencesInDefArg d StrictPos i e
                                 elims (i + 1) es
            elims 0 es

          _ -> do
            -- reportSLn "" 1 $ "NOTMUTUAL " ++ P.prettyShow d ++ " " ++ show (defArgOccurrences def)
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
                  ([]  , e:es) -> ret do ps <- liftTCM $ getOccurrencesFromType a
                                         elims' d i (drop i ps) (e:es)

            defOcc <- liftTCM $ mutualDefOcc d
            underOcc defOcc $ elims d (defType def) 0 (defArgOccurrences def) es

    Con _ _ es -> occurrences es -- András 2026-02-17: why not push something here?
    MetaV m es -> underPathSetOcc MetaArg Mixed (occurrences es)
    Pi a b     -> underPathOcc LeftOfArrow JustNeg (occurrences a) >> occurrences b
    Lam _ t    -> occurrences t
    Level l    -> occurrences l
    Lit{}      -> pure ()
    Sort{}     -> pure ()
    -- Jesper, 2020-01-12: this information is also used for the
    -- occurs check, so we need to look under DontCare (see #4371)
    DontCare t -> occurrences t
    Dummy{}    -> pure ()

addClauseArgMatches :: NAPs -> OccM ()
addClauseArgMatches ps = underPathSetOcc Matched Mixed $ go 0 ps where
  go :: Int -> NAPs -> OccM ()
  go i ps = expand \ret -> case ps of
    []   -> ret $ pure ()
    p:ps -> ret do
      liftTCM (properlyMatching (namedThing $ unArg p)) >>= \case
        True  -> do topDef <- asks topDef
                    addEdge (ArgNode topDef i)
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
              -- TODO: we get garbage Core for Pattern' foldl'
              let acc' = foldl'
                          (\acc j -> IntMap.insert (dbPatVarIndex j) (DefArgInEnv i []) acc)
                          acc (namedThing $ unArg p)
              in go (i + 1) ps acc'

      let items = collectArgs ps
      -- reportSLn "" 1 $ "NEW ITEMS |" ++ show items
      -- reportSLn "" 1 $ "PS " ++ P.prettyShow ps

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

mutualDefOcc :: QName -> TCM Occurrence
mutualDefOcc d = isDataOrRecordType d >>= \case
  Just IsData -> pure GuardPos
  _           -> pure StrictPos

-- | Backwards compatibility: add graph node with empty target map if it doesn't already exist.
--   TODO: this is probably a bug in the old code.
initNode :: Node -> OccM ()
initNode n = modify \m -> if Map.member n m then m else Map.insert n mempty m

-- | Compute occurrences in a given definition.
computeDefOccurrences :: QName -> OccM ()
computeDefOccurrences q = inConcreteOrAbstractMode q \def -> do
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

  defOcc <- liftTCM $ mutualDefOcc q
  underPathOcc (`InDefOf` q) defOcc $ case theDef def of

    Function{funClauses = cs} -> do

      cs <- liftTCM $ mapM etaExpandClause =<< instantiateFull cs
      performAnalysis <- liftTCM $ optOccurrence <$> pragmaOptions
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
                               addEdge (ArgNode d i)
                               go (i + 1) ps
          go 0 (namedClausePats cl)

    Datatype{dataClause = Just c} -> occurrences =<< liftTCM (instantiateFull c)

    Datatype{dataPars = np0, dataCons = cs, dataTranspIx = trx} -> do
      -- Andreas, 2013-02-27 (later edited by someone else): First,
      -- include each index of an inductive family.
      TelV telD _ <- liftTCM $ telView $ defType def
      -- Andreas, 2017-04-26, issue #2554: count first index as parameter if it has type Size.
      -- We compute sizeIndex=1 if first first index has type Size, otherwise sizeIndex==0
      sizeIndex <- liftTCM $ caseList (drop np0 $ telToList telD) (pure 0) \dom _ ->
                             caseMaybeM (isSizeType dom) (pure 0) \_ ->
                             pure 1

      let np = np0 + sizeIndex -- number of parameters

      -- add edge for size index, if it exists
      expand \ret -> case sizeIndex of
        1 -> ret $ addEdge (ArgNode q np0)
        _ -> ret $ pure ()

      -- add edges for indices
      underPathSetOcc IsIndex Mixed $
        rangeM_ np (size telD - 1) \i -> addEdge (ArgNode q i)


      -- Then, we compute the occurrences in the constructor types.
      --------------------------------------------------------------------------------

      -- If the data type has a transport constructor (i.e. it's an
      -- indexed family in cubical mode) we should also consider it for
      -- positivity.
      forMGood_ (maybeToList trx ++ cs) \c -> do
         -- Andreas, 2020-02-15, issue #4447:
         -- Allow UnconfimedReductions here to make sure we get the constructor type
         -- in same way as it was obtained when the data types was checked.
        (TelV tel t, bnd) <- liftTCM $ putAllowedReductions allReductions $
                                        telViewPathBoundary . defType =<< getConstInfo c
        let (tel0,tel1) = splitTelescopeAt np tel
        -- Do not collect occurrences in the data parameters.
        -- Normalization needed e.g. for test/succeed/Bush.agda.
        -- (Actually, for Bush.agda, reducing the parameters should be sufficient.)
        tel1' <- liftTCM $ addContext tel0 $ normalise tel1 -- András 2026-02-18: why addContext?
        pvars <- liftTCM $ paramsToDefArgs tel0

        -- o <- asks occ
        -- ls <- asks locals
        -- reportSLn "" 1 $ "CONARGTY " ++ show (P.prettyShow tel1', o, pvars,ls)

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

    Record{recClause = Just c} ->
      occurrences =<< liftTCM (instantiateFull c)

    Record{recPars = np, recTel = tel} -> do
      let (tel0, tel1) = splitTelescopeAt np tel
      pvars <- liftTCM $ paramsToDefArgs tel0
      local (\env -> env {topDefArgs = pvars}) do
        occurrences =<< liftTCM (addContext tel0 (normalise tel1))
        -- Andreas, 2017-01-01, issue #1899, treat like data types

    -- Arguments to other kinds of definitions are hard-wired.
    Constructor{}      -> mempty
    Axiom{}            -> mempty
    DataOrRecSig{}     -> mempty
    Primitive{}        -> mempty
    PrimitiveSort{}    -> mempty
    GeneralizableVar{} -> mempty
    AbstractDefn{}     -> __IMPOSSIBLE__


transposeGraph :: OccGraph -> OccGraph
transposeGraph m = foldl' ins mempty assocs where
  assocs = [(i, j, e) | (i, m) <- Map.toList m, (j, e) <- Map.toList m]
  ins acc (i, j, e) = addEdgeToGraph j i e acc


buildOccurrenceGraph :: Set QName -> TCM OccGraph
buildOccurrenceGraph topQs = do

  inf <- maybe Nothing (\x -> Just $! nameOfInf x) <$> coinductionKit

  let go :: [QName] -> OccGraph -> TCM OccGraph
      go qs acc = expand \ret -> case qs of
        []   -> ret $ pure acc
        q:qs -> ret do let env = OccEnv q [] inf 0 topQs (DefNode q) Root StrictPos
                       acc <- execStateT (runReaderT (computeDefOccurrences q) env) acc
                       go qs acc

  go (Set.toList topQs) mempty
