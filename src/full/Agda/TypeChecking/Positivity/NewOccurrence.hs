
{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}
{-# OPTIONS_GHC -fmax-valid-hole-fits=0 -fmax-relevant-binds=3 #-}

module Agda.TypeChecking.Positivity.NewOccurrence where

import Prelude hiding ( null, (!!) )

import Data.Foldable
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Interaction.Options.Base (optOccurrence, optPolarity)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Monad hiding (getOccurrencesFromType)
import Agda.TypeChecking.Patterns.Match ( properlyMatching )
import Agda.TypeChecking.Positivity.Occurrence (Occurrence(..), modalPolarityToOccurrence)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Syntax.Common
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Map qualified as Map
import Agda.Utils.Maybe
import Agda.Utils.SemiRing
import Agda.Utils.Size
import Agda.Utils.StrictReader
import Agda.Utils.StrictState

--------------------------------------------------------------------------------
{-
TODO:
handle Inf occurrence

mutable hashtable Graph
  (only need one SCC implementation and one BFS for positivity+error msg)

Possible issues in old impl:
- lack of Path/Occ handling in record constructors.
- In no-occurrence-analysis mode we only look at the first clause of functions to
  match the args
- computeDefOccurrences tel1' : why addContext?
-}


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

      -- it's a locally bound variable, all args are Mixed occurrence,
      -- we don't record an occurrence for the variable
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

addClauseArgMatches :: NAPs -> OccM ()
addClauseArgMatches = go 0 where
  go i []     = pure ()
  go i (p:ps) = do
    liftTCM (properlyMatching (namedThing $ unArg p)) >>= \case
      True  -> do topDef <- asks topDef
                  underPathOcc Matched Mixed $ addEdge (ArgNode topDef i)
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

      -- collect top def args from clause patterns
      let collectArgs :: Int -> NAPs -> [DefArgInEnv] -> [DefArgInEnv]
          collectArgs i []     acc = acc
          collectArgs i (p:ps) acc =
            let acc' = foldl' (\acc _ -> DefArgInEnv i [] : acc) acc
                              (namedThing $ unArg p)
            in collectArgs (i + 1) ps acc'

      -- process body
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
        go i []     acc = pure acc
        go i (a:as) acc = do occs <- getOccurrencesFromType (snd (unDom a))
                             go (i + 1) as (DefArgInEnv i occs : acc)

  underPath (`InDefOf` q) $ case theDef def of

    Function{funClauses = cs} -> do
      cs <- liftTCM $ mapM etaExpandClause =<< instantiateFull cs
      performAnalysis <- liftTCM $ optOccurrence <$> pragmaOptions
      if performAnalysis then do
        let clauses i []     = pure ()
            clauses i (c:cs) = underPath (`InClause` i) (occurrences c) >> clauses (i + 1) cs
        clauses 0 cs
      else case cs of
        []   -> __IMPOSSIBLE__
        -- András 2026-02-18: this looks dodgy?
        cl:_ -> addClauseArgMatches (namedClausePats cl)

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

      -- add edges for parameters
      forM_ [np0 .. np - 1] \i -> addEdge (ArgNode q i)

      -- add edges for indices
      underPath IsIndex $ forM_ [np .. size telD - 1] \i -> addEdge (ArgNode q i)


      -- Then, we compute the occurrences in the constructor types.
      --------------------------------------------------------------------------------

      -- If the data type has a transport constructor (i.e. it's an
      -- indexed family in cubical mode) we should also consider it for
      -- positivity.
      forM_ (maybeToList trx ++ cs) \c -> do
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
        local (\env -> env {topDefArgs = pvars, locals = np}) do

          -- edges in the types of constructor arguments
          underPath (`ConArgType`  c) $ occurrences tel1'
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
                  -- TODO: in the original code, we have
                  -- OccursAs (IndArgType c) . OnlyVarsUpTo np <$> getOccurrences telvars indices
                  -- The OnlyVarsUpTo seems to be pointless, but we'll see
                  underPath (`IndArgType` c) $ occurrences indices

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
      local (\env -> env {topDefArgs = pvars, locals = np}) do
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

buildOccurrenceGraph :: Set QName -> TCM OccGraph
buildOccurrenceGraph topQs = do

  inf <- fmap nameOfInf <$> coinductionKit

  -- TODO: if we want to preserve old debug printing behavior,
  -- we can collect graphs separately here and then merge them
  let go :: [QName] -> OccGraph -> TCM OccGraph
      go []     acc = pure acc
      go (q:qs) acc = do
        let env = OccEnv q [] inf 0 topQs (DefNode q) Root StrictPos
        acc <- execStateT (runReaderT (computeDefOccurrences q) env) acc
        go qs acc

  go (Set.toList topQs) mempty
