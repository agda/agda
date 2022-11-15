{-# LANGUAGE NondecreasingIndentation #-}

-- | Check that a datatype is strictly positive.
module Agda.TypeChecking.Positivity where

import Prelude hiding ( null, (!!) )

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Monad.Reader ( MonadReader(..), asks, Reader, runReader )

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

import Debug.Trace

import Agda.Syntax.Common
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position (HasRange(..), noRange)
import Agda.TypeChecking.Datatypes ( isDataOrRecordType )
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

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

import Agda.Utils.Impossible

type Graph n e = Graph.Graph n e

-- | Check that the datatypes in the mutual block containing the given
--   declarations are strictly positive.
--
--   Find polarity of datatypes parameters and indices.
--
--   Also add information about positivity and recursivity of records
--   to the signature.
--
checkStrictlyPositive :: Info.MutualInfo -> Set QName -> TCM ()
checkStrictlyPositive mi qset = do
  -- compute the occurrence graph for qs
  let qs = Set.toList qset
  reportSDoc "tc.pos.tick" 100 $ "positivity of" <+> prettyTCM qs
  g <- buildOccurrenceGraph qset
  let (gstar, sccs) =
        Graph.gaussJordanFloydWarshallMcNaughtonYamada $ fmap occ g
  reportSDoc "tc.pos.tick" 100 $ "constructed graph"
  reportSLn "tc.pos.graph" 5 $ "Positivity graph: N=" ++ show (size $ Graph.nodes g) ++
                               " E=" ++ show (length $ Graph.edges g)
  reportSDoc "tc.pos.graph" 10 $ vcat
    [ "positivity graph for" <+> fsep (map prettyTCM qs)
    , nest 2 $ prettyTCM g
    ]
  reportSLn "tc.pos.graph" 5 $
    "Positivity graph (completed): E=" ++ show (length $ Graph.edges gstar)
  reportSDoc "tc.pos.graph" 50 $ vcat
    [ "transitive closure of positivity graph for" <+>
      prettyTCM qs
    , nest 2 $ prettyTCM gstar
    ]

  -- remember argument occurrences for qs in the signature
  setArgOccs qset qs gstar
  reportSDoc "tc.pos.tick" 100 $ "set args"

  -- check positivity for all strongly connected components of the graph for qs
  reportSDoc "tc.pos.graph.sccs" 10 $ do
    let (triv, others) = partitionEithers $ for sccs $ \case
          AcyclicSCC v -> Left v
          CyclicSCC vs -> Right vs
    sep [ text $ show (length triv) ++ " trivial sccs"
        , text $ show (length others) ++ " non-trivial sccs with lengths " ++
            show (map length others)
        ]
  reportSLn "tc.pos.graph.sccs" 15 $
    "  sccs = " ++ prettyShow [ scc | CyclicSCC scc <- sccs ]

  -- #7133: Note that the graph doesn't necessarily contain all of qs in the case where there are no
  -- occurrences of a name, but we still need to setMutual for them.
  let sccMap = Map.unions [ case scc of
                              AcyclicSCC (DefNode q) -> Map.singleton q []
                              AcyclicSCC ArgNode{}   -> mempty
                              CyclicSCC scc          -> Map.fromList [ (q, qs) | q <- qs ]
                                where qs = [ q | DefNode q <- scc ]
                          | scc <- sccs ]
  inAbstractMode $ forM_ qs $ \ q ->
    whenM (isNothing <$> getMutual q) $ do
      let qs = fromMaybe [] $ Map.lookup q sccMap
      reportSLn "tc.pos.mutual" 10 $ "setting " ++ prettyShow q ++ " to " ++
                                     if | null qs        -> "non-recursive"
                                        | length qs == 1 -> "recursive"
                                        | otherwise      -> "mutually recursive"
      setMutual q qs

  mapM_ (checkPos g gstar) qs
  reportSDoc "tc.pos.tick" 100 $ "checked positivity"

  where
    checkPos :: Graph Node (Edge OccursWhere) ->
                Graph Node Occurrence ->
                QName -> TCM ()
    checkPos g gstar q = inConcreteOrAbstractMode q $ \ def -> do
      -- we check positivity only for data or record definitions
      whenJust (isDatatype def) $ \ dr -> do
        reportSDoc "tc.pos.check" 10 $ "Checking positivity of" <+> prettyTCM q

        let loop :: Maybe Occurrence
            loop = Graph.lookup (DefNode q) (DefNode q) gstar

            g' :: Graph Node (Edge (Seq OccursWhere))
            g' = fmap (fmap DS.singleton) g

            -- Note the property
            -- Internal.Utils.Graph.AdjacencyMap.Unidirectional.prop_productOfEdgesInBoundedWalk,
            -- which relates productOfEdgesInBoundedWalk to
            -- gaussJordanFloydWarshallMcNaughtonYamada.

            reason bound =
              case productOfEdgesInBoundedWalk
                     occ g' (DefNode q) (DefNode q) bound of
                Just (Edge _ how) -> how
                Nothing           -> __IMPOSSIBLE__

            how :: String -> Occurrence -> TCM Doc
            how msg bound = fsep $
                  [prettyTCM q] ++ pwords "is" ++
                  pwords (msg ++ ", because it occurs") ++
                  [prettyTCM (reason bound)]

        -- if we have a negative loop, raise error

        -- ASR (23 December 2015). We don't raise a strictly positive
        -- error if the NO_POSITIVITY_CHECK pragma was set on in the
        -- mutual block. See Issue 1614.
        when (Info.mutualPositivityCheck mi == YesPositivityCheck) $
          whenM positivityCheckEnabled $
            case loop of
            Just o | o <= JustPos ->
              warning $ NotStrictlyPositive q (reason JustPos)
            _ -> return ()

        -- if we find an unguarded record, mark it as such
        case dr of
          IsData -> return ()
          IsRecord pat -> case loop of
            Just o | o <= StrictPos -> do
              reportSDoc "tc.pos.record" 5 $ how "not guarded" StrictPos
              unguardedRecord q pat
              checkInduction q
            -- otherwise, if the record is recursive, mark it as well
            Just o | o <= GuardPos -> do
              reportSDoc "tc.pos.record" 5 $ how "recursive" GuardPos
              recursiveRecord q
              checkInduction q
            -- If the record is not recursive, switch on eta
            -- unless it is coinductive or a no-eta-equality record.
            Nothing -> do
              reportSDoc "tc.pos.record" 10 $
                "record type " <+> prettyTCM q <+>
                "is not recursive"
              nonRecursiveRecord q
            _ -> return ()

    checkInduction :: QName -> TCM ()
    checkInduction q =
      -- ASR (01 January 2016). We don't raise this error if the
      -- NO_POSITIVITY_CHECK pragma was set on in the record. See
      -- Issue 1760.
      when (Info.mutualPositivityCheck mi == YesPositivityCheck) $
        whenM positivityCheckEnabled $ do
        -- Check whether the recursive record has been declared as
        -- 'Inductive' or 'Coinductive'.  Otherwise, error.
        unlessM (isJust . recInduction . theDef <$> getConstInfo q) $
          setCurrentRange (nameBindingSite $ qnameName q) $
            typeError $ RecursiveRecordNeedsInductivity q

    occ (Edge o _) = o

    isDatatype :: Definition -> Maybe DataOrRecord
    isDatatype def = do
      case theDef def of
        Datatype{dataClause = Nothing} -> Just IsData
        Record  {recClause  = Nothing, recPatternMatching } -> Just $ IsRecord recPatternMatching
        _ -> Nothing

    -- Set the polarity of the arguments to a couple of definitions
    setArgOccs :: Set QName -> [QName] -> Graph Node Occurrence -> TCM ()
    setArgOccs qset qs g = do
      -- Andreas, 2018-05-11, issue #3049: we need to be pessimistic about
      -- argument polarity beyond the formal arity of the function.
      --
      -- -- Compute a map from each name in q to the maximal argument index
      -- let maxs = Map.fromListWith max
      --      [ (q, i) | ArgNode q i <- Set.toList $ Graph.nodes g, q `Set.member` qset ]
      forM_ qs $ \ q -> inConcreteOrAbstractMode q $ \ def -> when (hasDefinition $ theDef def) $ do
        reportSDoc "tc.pos.args" 10 $ "checking args of" <+> prettyTCM q
        n <- getDefArity def
        -- If there is no outgoing edge @ArgNode q i@, all @n@ arguments are @Unused@.
        -- Otherwise, we obtain the occurrences from the Graph.
        let findOcc i = fromMaybe Unused $ Graph.lookup (ArgNode q i) (DefNode q) g
            args = -- caseMaybe (Map.lookup q maxs) (replicate n Unused) $ \ m ->
              map findOcc [0 .. n-1]  -- [0 .. max m (n - 1)] -- triggers issue #3049
        reportSDoc "tc.pos.args" 10 $ sep
          [ "args of" <+> prettyTCM q <+> "="
          , nest 2 $ prettyList $ map prettyTCM args
          ]
        -- The list args can take a long time to compute, but contains
        -- small elements, and is stored in the interface (right?), so
        -- it is computed deep-strictly.
        setArgOccurrences q $!! args
      where
      -- Andreas, 2018-11-23, issue #3404
      -- Only assign argument occurrences to things which have a definition.
      -- Things without a definition would be judged "constant" in all arguments,
      -- since no occurrence could possibly be found, naturally.
      hasDefinition :: Defn -> Bool
      hasDefinition = \case
        Axiom{}            -> False
        DataOrRecSig{}     -> False
        GeneralizableVar{} -> False
        AbstractDefn{}     -> False
        Primitive{}        -> False
        PrimitiveSort{}    -> False
        Constructor{}      -> False
        Function{}         -> True
        Datatype{}         -> True
        Record{}           -> True

getDefArity :: Definition -> TCM Int
getDefArity def = do
  subtract (projectionArgs def) <$> arity' (defType def)
  where
  -- A variant of "\t -> arity <$> instantiateFull t".
  arity' :: Type -> TCM Int
  arity' t = do
    t <- instantiate t
    case unEl t of
      Pi _ t -> succ <$> arity' (unAbs t)
      _      -> return 0

-- Computing occurrences --------------------------------------------------

data Item = AnArg Nat [Occurrence]
          | ADef QName
  deriving (Eq, Ord, Show)

instance HasRange Item where
  getRange (AnArg _ _) = noRange
  getRange (ADef qn)   = getRange qn

instance Pretty Item where
  prettyPrec p (AnArg i t) = P.mparens (p > 9) $ "AnArg" P.<+> P.pretty t
  prettyPrec p (ADef qn) = P.mparens (p > 9) $ "ADef"  P.<+> P.pretty qn

type Occurrences = Map Item [OccursWhere]

-- | Used to build 'Occurrences' and occurrence graphs.
data OccurrencesBuilder
  = Concat [OccurrencesBuilder]
  | OccursAs Where OccurrencesBuilder
  | OccursHere Item
  | OnlyVarsUpTo Nat OccurrencesBuilder
    -- ^ @OnlyVarsUpTo n occs@ discards occurrences of de Bruijn index
    -- @>= n@.

-- | Used to build 'Occurrences' and occurrence graphs.
data OccurrencesBuilder'
  = Concat' [OccurrencesBuilder']
  | OccursAs' Where OccurrencesBuilder'
  | OccursHere' Item

-- | The semigroup laws only hold up to flattening of 'Concat'.
instance Semigroup OccurrencesBuilder where
  occs1 <> occs2 = Concat [occs1, occs2]

-- | The monoid laws only hold up to flattening of 'Concat'.
instance Monoid OccurrencesBuilder where
  mempty  = Concat []
  mappend = (<>)
  mconcat = Concat

-- | Removes 'OnlyVarsUpTo' entries.
preprocess :: OccurrencesBuilder -> OccurrencesBuilder'
preprocess ob = case pp Nothing ob of
  Nothing -> Concat' []
  Just ob -> ob
  where
  pp :: Maybe Nat  -- Variables larger than or equal to this number, if any,
                   -- are not retained.
     -> OccurrencesBuilder
     -> Maybe OccurrencesBuilder'
  pp !m = \case
    Concat obs -> case mapMaybe (pp m) obs of
      []  -> Nothing
      obs -> return (Concat' obs)

    OccursAs w ob -> OccursAs' w <$> pp m ob

    OnlyVarsUpTo n ob -> pp (Just $! maybe n (min n) m) ob

    OccursHere i -> do
      guard keep
      return (OccursHere' i)
      where
      keep = case (m, i) of
        (Nothing, _)      -> True
        (_, ADef _)       -> True
        (Just m, AnArg i _) -> i < m

-- | An interpreter for 'OccurrencesBuilder'.
--
-- WARNING: There can be lots of sharing between the generated
-- 'OccursWhere' entries. Traversing all of these entries could be
-- expensive. (See 'computeEdges' for an example.)
flatten :: OccurrencesBuilder -> Map Item Integer
flatten =
  Map.fromListWith (+) .
  flip flatten' [] .
  preprocess
  where
  flatten'
    :: OccurrencesBuilder'
    -> [(Item, Integer)]
    -> [(Item, Integer)]
  flatten' (Concat' obs)    = foldr (\occs f -> flatten' occs . f) id obs
  flatten' (OccursAs' _ ob) = flatten' ob
  flatten' (OccursHere' i)  = ((i, 1) :)

-- | Context for computing occurrences.
data OccEnv = OccEnv
  { vars :: [Maybe Item]
    -- ^ Items corresponding to the free variables.
    --
    --   Potential invariant: It seems as if the list has the form
    --   @'genericReplicate' n 'Nothing' ++ 'map' ('Just' . 'AnArg') is@,
    --   for some @n@ and @is@, where @is@ is decreasing
    --   (non-strictly).
  , inf  :: Maybe QName
    -- ^ Name for ∞ builtin.
  }

-- | Monad for computing occurrences.
type OccM = Reader OccEnv

instance (Semigroup a, Monoid a) => Monoid (OccM a) where
  mempty  = return mempty
  mappend = (<>)
  mconcat = mconcat <.> sequence

withExtendedOccEnv :: Maybe Item -> OccM a -> OccM a
withExtendedOccEnv i = withExtendedOccEnv' [i]

withExtendedOccEnv' :: [Maybe Item] -> OccM a -> OccM a
withExtendedOccEnv' is = local $ \ e -> e { vars = is ++ vars e }

-- | Running the monad
getOccurrences
  :: (Show a, PrettyTCM a, ComputeOccurrences a)
  => [Maybe Item]  -- ^ Extension of the 'OccEnv', usually a local variable context.
  -> a
  -> TCM OccurrencesBuilder
getOccurrences vars a = do
  reportSDoc "tc.pos.occ" 70 $ "computing occurrences in " <+> text (show a)
  reportSDoc "tc.pos.occ" 20 $ "computing occurrences in " <+> prettyTCM a
  reportSDoc "tc.pos.var" 20 $ "variables in context: " <+> pretty vars
  runReader (occurrences a) . OccEnv vars . fmap nameOfInf <$> coinductionKit

class ComputeOccurrences a where
  occurrences :: a -> OccM OccurrencesBuilder

  default occurrences :: (Foldable t, ComputeOccurrences b, t b ~ a) => a -> OccM OccurrencesBuilder
  occurrences = foldMap occurrences

instance ComputeOccurrences Clause where
  occurrences cl = do
    let ps    = namedClausePats cl
        items = IntMap.elems $ patItems ps -- sorted from low to high DBI
    -- TODO #3733: handle hcomp/transp clauses properly
    if hasDefP ps then return mempty else do
    (Concat (mapMaybe matching (zip [0..] ps)) <>) <$> do
      withExtendedOccEnv' items $
        occurrences $ clauseBody cl
    where
      matching (i, p)
        | properlyMatching (namedThing $ unArg p) =
            Just $ OccursAs Matched $ OccursHere $ AnArg i []
        | otherwise                  = Nothing

      -- @patItems ps@ creates a map from the pattern variables of @ps@
      -- to the index of the argument they are bound in.
      patItems ps = mconcat $ zipWith patItem [0..] ps

      -- @patItem i p@ assigns index @i@ to each pattern variable in @p@
      patItem :: Int -> NamedArg DeBruijnPattern -> IntMap (Maybe Item)
      patItem i p = Fold.foldMap makeEntry ixs
        where
          ixs = map dbPatVarIndex $ lefts $ map unArg $ patternVars $ namedThing <$> p

          makeEntry x = singleton (x, Just $ AnArg i [])

instance ComputeOccurrences Term where
  occurrences v = case unSpine v of
    Var i args ->
      asks (occI . vars) <> do
        occs <- mapM occurrences args

        -- Lucas, 2022-12-01: Now, the variable may have the polarities of its arguments
        -- stored in the context (iff the variable refers to a datatype parameter)
        item <- reader ((!! i) . vars)

        let getPol i = fromMaybe Mixed $ do
              AnArg _ aoccs <- item
              aoccs !!! i

        return $ Concat $ zipWith (\i -> OccursAs (VarArg (getPol i) i)) [0..] occs
      where
        occI vars = maybe mempty OccursHere $ indexWithDefault unbound vars i
        unbound = flip trace __IMPOSSIBLE__ $
              "impossible: occurrence of de Bruijn index " ++ show i ++
              " in vars " ++ show vars ++ " is unbound"

    Def d args   -> do
      inf <- asks inf
      let occsAs = if Just d /= inf then OccursAs . DefArg d else \ n ->
            -- the principal argument of builtin INF (∞) is the second (n==1)
            -- the first is a level argument (n==0, counting from 0!)
            if n == 1 then OccursAs UnderInf else OccursAs (DefArg d n)
      occs <- mapM occurrences args
      return . Concat $ OccursHere (ADef d) : zipWith occsAs [0..] occs

    Con _ _ args -> occurrences args
    MetaV _ args -> OccursAs MetaArg <$> occurrences args
    Pi a b       -> (OccursAs LeftOfArrow <$> occurrences a) <> occurrences b
    Lam _ b      -> occurrences b
    Level l      -> occurrences l
    Lit{}        -> mempty
    Sort{}       -> mempty
    -- Jesper, 2020-01-12: this information is also used for the
    -- occurs check, so we need to look under DontCare (see #4371)
    DontCare v   -> occurrences v
    Dummy{}      -> mempty

instance ComputeOccurrences Level where
  occurrences (Max _ as) = occurrences as

instance ComputeOccurrences PlusLevel where
  occurrences (Plus _ l) = occurrences l

instance ComputeOccurrences Type where
  occurrences (El _ v) = occurrences v

instance ComputeOccurrences a => ComputeOccurrences (Tele a) where
  occurrences EmptyTel        = mempty
  occurrences (ExtendTel a b) = occurrences (a, b)

instance ComputeOccurrences a => ComputeOccurrences (Abs a) where
  occurrences (Abs   _ b) = withExtendedOccEnv Nothing $ occurrences b
  occurrences (NoAbs _ b) = occurrences b

instance ComputeOccurrences a => ComputeOccurrences (Elim' a) where
  occurrences Proj{}         = __IMPOSSIBLE__  -- unSpine
  occurrences (Apply a)      = occurrences a
  occurrences (IApply x y a) = occurrences (x,(y,a)) -- TODO Andrea: conservative

instance ComputeOccurrences a => ComputeOccurrences (Arg a)   where
instance ComputeOccurrences a => ComputeOccurrences (Dom a)   where
instance ComputeOccurrences a => ComputeOccurrences [a]       where
instance ComputeOccurrences a => ComputeOccurrences (Maybe a) where

instance (ComputeOccurrences a, ComputeOccurrences b) => ComputeOccurrences (a, b) where
  occurrences (x, y) = occurrences x <> occurrences y

-- | Computes the number of occurrences of different 'Item's in the
-- given definition.
--
-- WARNING: There can be lots of sharing between the 'OccursWhere'
-- entries. Traversing all of these entries could be expensive. (See
-- 'computeEdges' for an example.)
computeOccurrences :: QName -> TCM (Map Item Integer)
computeOccurrences q = flatten <$> computeOccurrences' q

-- | Returns the occurences given explicitely as polarity annotations in the function type
getOccurrencesFromType :: Type -> TCM [Occurrence]
getOccurrencesFromType t = do
  telList <- telToList . theTel <$> telView t
  return $ modalPolarityToOccurrence . modPolarityAnn . getModalPolarity <$> telList

-- | Computes the occurrences in the given definition.
computeOccurrences' :: QName -> TCM OccurrencesBuilder
computeOccurrences' q = inConcreteOrAbstractMode q $ \ def -> do
  reportSDoc "tc.pos" 25 $ do
    let a = defAbstract def
    m <- asksTC envAbstractMode
    cur <- asksTC envCurrentModule
    o <- asksTC envCurrentOpaqueId
    "computeOccurrences" <+> prettyTCM q <+> text (show a) <+> text (show o) <+> text (show m)
      <+> prettyTCM cur
  OccursAs (InDefOf q) <$> case theDef def of

    Function{funClauses = cs} -> do
      cs <- mapM etaExpandClause =<< instantiateFull cs
      Concat . zipWith (OccursAs . InClause) [0..] <$>
        mapM (getOccurrences []) cs

    Datatype{dataClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Datatype{dataPars = np0, dataCons = cs} -> do
      -- Andreas, 2013-02-27 (later edited by someone else): First,
      -- include each index of an inductive family.
      TelV telD _ <- telView $ defType def
      -- Andreas, 2017-04-26, issue #2554: count first index as parameter if it has type Size.
      -- We compute sizeIndex=1 if first first index has type Size, otherwise sizeIndex==0
      sizeIndex <- caseList (drop np0 $ telToList telD) (return 0) $ \ dom _ -> do
        caseMaybeM (isSizeType dom) (return 0) $ \ _ -> return 1
      let np = np0 + sizeIndex
      let xs = [np .. size telD - 1] -- argument positions corresponding to indices

      let ioccs = Concat $ map (\i -> OccursHere $ AnArg i []) [np0 .. np - 1]
                        ++ map (\i -> OccursAs IsIndex $ OccursHere $ AnArg i []) xs

      -- Then, we compute the occurrences in the constructor types.
      let conOcc c = do
            -- Andreas, 2020-02-15, issue #4447:
            -- Allow UnconfimedReductions here to make sure we get the constructor type
            -- in same way as it was obtained when the data types was checked.
            (TelV tel t, bnd) <- putAllowedReductions allReductions $
              telViewUpToPathBoundary' (-1) . defType =<< getConstInfo c
            let (tel0,tel1) = splitTelescopeAt np tel
            -- Do not collect occurrences in the data parameters.
            -- Normalization needed e.g. for test/succeed/Bush.agda.
            -- (Actually, for Bush.agda, reducing the parameters should be sufficient.)
            tel1' <- addContext tel0 $ normalise $ tel1

            -- Make parameters into context items, with polarity info
            pvars <- parametersToItems tel0 np
            let telvars = replicate (size tel1') Nothing ++ pvars

            reportSLn "tc.pos.params" 50 $ "Adding datatypes parameters in context " ++ prettyShow pvars

            -- Occurrences in the types of the constructor arguments.
            (OccursAs (ConArgType c) <$> getOccurrences pvars tel1') <>
              (OccursAs (ConEndpoint c) <$> getOccurrences telvars bnd) <> do
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
                      OccursAs (IndArgType c) . OnlyVarsUpTo np <$> getOccurrences telvars indices
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
      mconcat $ pure ioccs : map conOcc cs

    Record{recClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Record{recPars = np, recTel = tel} -> do
      let (tel0,tel1) = splitTelescopeAt np tel
      pvars <- parametersToItems tel0 np
      getOccurrences pvars =<< addContext tel0 (normalise tel1) -- Andreas, 2017-01-01, issue #1899, treat like data types

    -- Arguments to other kinds of definitions are hard-wired.
    Constructor{}      -> mempty
    Axiom{}            -> mempty
    DataOrRecSig{}     -> mempty
    Primitive{}        -> mempty
    PrimitiveSort{}    -> mempty
    GeneralizableVar{} -> mempty
    AbstractDefn{}     -> __IMPOSSIBLE__
  where
    parametersToItems :: Telescope -> Nat -> TCM [Maybe Item]
    parametersToItems tel n = reverse <$>
      zipWithM (\i -> fmap (Just . AnArg i) . getOccurrencesFromType)
        [0 .. n -1]
        (snd . unDom <$> telToList tel)


-- Building the occurrence graph ------------------------------------------

data Node = DefNode !QName
          | ArgNode !QName !Nat
  deriving (Eq, Ord)

-- | Edge labels for the positivity graph.
data Edge a = Edge !Occurrence a
  deriving (Eq, Ord, Show, Functor)

-- | Merges two edges between the same source and target.

mergeEdges :: Edge a -> Edge a -> Edge a
mergeEdges _                    e@(Edge Mixed _)     = e -- dominant
mergeEdges e@(Edge Mixed _)     _                    = e
mergeEdges (Edge Unused _)      e                    = e -- neutral
mergeEdges e                    (Edge Unused _)      = e
mergeEdges (Edge JustNeg _)     e@(Edge JustNeg _)   = e
mergeEdges _                    e@(Edge JustNeg w)   = Edge Mixed w
mergeEdges e@(Edge JustNeg w)   _                    = Edge Mixed w
mergeEdges _                    e@(Edge JustPos _)   = e -- dominates strict pos.
mergeEdges e@(Edge JustPos _)   _                    = e
mergeEdges _                    e@(Edge StrictPos _) = e -- dominates 'GuardPos'
mergeEdges e@(Edge StrictPos _) _                    = e
mergeEdges (Edge GuardPos _)    e@(Edge GuardPos _)  = e

-- | These operations form a semiring if we quotient by the relation
-- \"the 'Occurrence' components are equal\".

instance SemiRing (Edge (Seq OccursWhere)) where
  ozero = Edge ozero DS.empty
  oone  = Edge oone  DS.empty

  oplus = mergeEdges

  otimes (Edge o1 w1) (Edge o2 w2) = Edge (otimes o1 o2) (w1 DS.>< w2)

-- | WARNING: There can be lots of sharing between the 'OccursWhere'
-- entries in the edges. Traversing all of these entries could be
-- expensive. (See 'computeEdges' for an example.)
buildOccurrenceGraph :: Set QName -> TCM (Graph Node (Edge OccursWhere))
buildOccurrenceGraph qs =
  Graph.fromEdgesWith mergeEdges . concat <$>
    mapM defGraph (Set.toList qs)
  where
    defGraph :: QName -> TCM [Graph.Edge Node (Edge OccursWhere)]
    defGraph q = inConcreteOrAbstractMode q $ \ _def -> do
      occs <- computeOccurrences' q

      reportSDoc "tc.pos.occs" 40 $
        (("Occurrences in" <+> prettyTCM q) <> ":")
          $+$
        nest 2 (vcat $
           map (\(i, n) ->
                   (pretty i <> ":") <+> text (show n) <+>
                   "occurrences") $
           List.sortBy (compare `on` snd) $
           Map.toList (flatten occs))

      -- Placing this line before the reportSDoc lines above creates a
      -- space leak: occs is retained for too long.
      es <- computeEdges qs q occs

      reportSDoc "tc.pos.occs.edges" 60 $
        "Edges:"
          $+$
        nest 2 (vcat $
           map (\e ->
                   let Edge o w = Graph.label e in
                   prettyTCM (Graph.source e) <+>
                   "-[" <+> (return (P.pretty o) <> ",") <+>
                                 return (P.pretty w) <+> "]->" <+>
                   prettyTCM (Graph.target e))
               es)

      return es

-- | Computes all non-'ozero' occurrence graph edges represented by
-- the given 'OccurrencesBuilder'.
--
-- WARNING: There can be lots of sharing between the 'OccursWhere'
-- entries in the edges. Traversing all of these entries could be
-- expensive. For instance, for the function @F@ in
-- @benchmark/misc/SlowOccurrences.agda@ a large number of edges from
-- the argument @X@ to the function @F@ are computed. These edges have
-- polarity 'StrictPos', 'JustNeg' or 'JustPos', and contain the
-- following 'OccursWhere' elements:
--
-- * @'OccursWhere' _ 'DS.empty' ('DS.fromList' ['InDefOf' "F", 'InClause' 0])@,
--
-- * @'OccursWhere' _ 'DS.empty' ('DS.fromList' ['InDefOf' "F", 'InClause' 0, 'LeftOfArrow'])@,
--
-- * @'OccursWhere' _ 'DS.empty' ('DS.fromList' ['InDefOf' "F", 'InClause' 0, 'LeftOfArrow', 'LeftOfArrow'])@,
--
-- * @'OccursWhere' _ 'DS.empty' ('DS.fromList' ['InDefOf' "F", 'InClause' 0, 'LeftOfArrow', 'LeftOfArrow', 'LeftOfArrow'])@,
--
-- * and so on.
computeEdges
  :: Set QName
     -- ^ The names in the current mutual block.
  -> QName
     -- ^ The current name.
  -> OccurrencesBuilder
  -> TCM [Graph.Edge Node (Edge OccursWhere)]
computeEdges muts q ob =
  ($ []) <$> mkEdge StrictPos (preprocess ob)
                    __IMPOSSIBLE__ DS.empty DS.empty
  where
  mkEdge
     :: Occurrence
     -> OccurrencesBuilder'
     -> Node          -- The current target node.
     -> DS.Seq Where  -- 'Where' information encountered before the current target
                      -- node was (re)selected.
     -> DS.Seq Where  -- 'Where' information encountered after the current target
                      -- node was (re)selected.
     -> TCM ([Graph.Edge Node (Edge OccursWhere)] ->
             [Graph.Edge Node (Edge OccursWhere)])
  mkEdge !pol ob to cs os = case ob of
    Concat' obs ->
      foldr (liftM2 (.)) (return id)
            [ mkEdge pol ob to cs os | ob <- obs ]

    OccursAs' w ob -> do
      (to', pol) <- mkEdge' to pol w
      let mk = mkEdge pol ob
      case to' of
        Nothing -> mk to cs            (os DS.|> w)
        Just to -> mk to (cs DS.>< os) (DS.singleton w)

    OccursHere' i ->
      let o = OccursWhere (getRange i) cs os in
      case i of
        AnArg i t ->
          return $ applyUnless (null pol) (Graph.Edge
            { Graph.source = ArgNode q i
            , Graph.target = to
            , Graph.label  = Edge pol o
            } :)
        ADef q' ->
          -- Andreas, 2017-04-26, issue #2555
          -- Skip nodes pointing outside the mutual block.
          return $ applyUnless (null pol || Set.notMember q' muts)
            (Graph.Edge
               { Graph.source = DefNode q'
               , Graph.target = to
               , Graph.label  = Edge pol o
               } :)

  -- This function might return a new target node.
  mkEdge'
    :: Node  -- The current target node.
    -> Occurrence
    -> Where
    -> TCM (Maybe Node, Occurrence)
  mkEdge' to !pol = \case
    VarArg p i     -> addPol p
    MetaArg        -> mixed
    LeftOfArrow    -> negative
    DefArg d i     -> do
      pol' <- isGuarding d
      if Set.member d muts
        then return (Just (ArgNode d i), pol')
        else addPol =<< otimes pol' <$> getArgOccurrence d i
    UnderInf       -> addPol GuardPos -- Andreas, 2012-06-09: ∞ is guarding
    ConArgType _   -> keepGoing
    IndArgType _   -> mixed
    ConEndpoint _  -> keepGoing
    InClause _     -> keepGoing
    Matched        -> mixed -- consider arguments matched against as used
    IsIndex        -> mixed -- And similarly for indices.
    InDefOf d      -> do
      pol' <- isGuarding d
      return (Just (DefNode d), pol')
    where
    keepGoing   = return (Nothing, pol)
    mixed       = return (Nothing, Mixed)
    negative    = return (Nothing, otimes pol JustNeg)
    addPol pol' = return (Nothing, otimes pol pol')

  isGuarding d = do
    isDataOrRecordType d <&> \case
      Just IsData -> GuardPos  -- a datatype is guarding
      _           -> StrictPos

-- Pretty-printing -----------------------------------------------------

instance Pretty Node where
  pretty = \case
    DefNode q   -> P.pretty q
    ArgNode q i -> P.pretty q <> P.text ("." ++ show i)

instance PrettyTCM Node where
  prettyTCM = return . P.pretty

instance PrettyTCMWithNode (Edge OccursWhere) where
  prettyTCMWithNode (WithNode n (Edge o w)) = vcat
    [ prettyTCM o <+> prettyTCM n
    , nest 2 $ return $ P.pretty w
    ]

instance PrettyTCM (Seq OccursWhere) where
  prettyTCM =
    fmap snd . prettyOWs . map adjustLeftOfArrow . uniq . Fold.toList
    where
      nth 0 = pwords "first"
      nth 1 = pwords "second"
      nth 2 = pwords "third"
      nth n = pwords $ show (n + 1) ++ "th"

      -- Removes consecutive duplicates.
      uniq :: [OccursWhere] -> [OccursWhere]
      uniq = map List1.head . List1.groupBy ((==) `on` snd')
        where
        snd' (OccursWhere _ _ ws) = ws

      prettyOWs :: MonadPretty m => [OccursWhere] -> m (String, Doc)
      prettyOWs []  = __IMPOSSIBLE__
      prettyOWs [o] = do
        (s, d) <- prettyOW o
        return (s, d <> ".")
      prettyOWs (o:os) = do
        (s1, d1) <- prettyOW  o
        (s2, d2) <- prettyOWs os
        return (s1, d1 <> ("," P.<+> "which" P.<+> P.text s2 P.$$ d2))

      prettyOW :: MonadPretty m => OccursWhere -> m (String, Doc)
      prettyOW (OccursWhere _ cs ws)
        | null cs   = prettyWs ws
        | otherwise = do
            (s, d1) <- prettyWs ws
            (_, d2) <- prettyWs cs
            return (s, d1 P.$$ "(" <> d2 <> ")")

      prettyWs :: MonadPretty m => Seq Where -> m (String, Doc)
      prettyWs ws = case Fold.toList ws of
        [InDefOf d, IsIndex] ->
          (,) "is" <$> fsep (pwords "an index of" ++ [prettyTCM d])
        _ ->
          (,) "occurs" <$>
            Fold.foldrM (\w d -> return d $$ fsep (prettyW w)) empty ws

      prettyW :: MonadPretty m => Where -> [m Doc]
      prettyW = \case
        LeftOfArrow  -> pwords "to the left of an arrow"
        DefArg q i   -> pwords "in the" ++ nth i ++ pwords "argument of" ++
                          [prettyTCM q]
        UnderInf     -> pwords "under" ++
                        [do -- this cannot fail if an 'UnderInf' has been generated
                            inf <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInf
                            prettyTCM inf]
        VarArg p i   -> pwords "in an argument of a bound variable at position" ++ [prettyTCM i]
                        ++ pwords "which uses its argument with polarity" ++ [ pretty p ]
        MetaArg      -> pwords "in an argument of a metavariable"
        ConArgType c -> pwords "in the type of the constructor" ++ [prettyTCM c]
        IndArgType c -> pwords "in an index of the target type of the constructor" ++ [prettyTCM c]
        ConEndpoint c
                     -> pwords "in an endpoint of the target of the" ++
                        pwords "higher constructor" ++ [prettyTCM c]
        InClause i   -> pwords "in the" ++ nth i ++ pwords "clause"
        Matched      -> pwords "as matched against"
        IsIndex      -> pwords "as an index"
        InDefOf d    -> pwords "in the definition of" ++ [prettyTCM d]

      adjustLeftOfArrow :: OccursWhere -> OccursWhere
      adjustLeftOfArrow (OccursWhere r cs os) =
        OccursWhere r (DS.filter (not . isArrow) cs) $
          noArrows
            DS.><
          case DS.viewl startsWithArrow of
            DS.EmptyL  -> DS.empty
            w DS.:< ws -> w DS.<| DS.filter (not . isArrow) ws
        where
        (noArrows, startsWithArrow) = DS.breakl isArrow os

        isArrow LeftOfArrow{} = True
        isArrow _             = False
