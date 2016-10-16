{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Check that a datatype is strictly positive.
module Agda.TypeChecking.Positivity where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Monad.Reader
import Control.Monad.State (get)

import Data.Either
import qualified Data.Foldable as Fold
import Data.Function
import Data.Graph (SCC(..), flattenSCC)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List as List hiding (null)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid (mconcat)
import qualified Data.Sequence as DS
import Data.Set (Set)
import qualified Data.Set as Set

import Debug.Trace

import Agda.Syntax.Common
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position (fuseRange, Range, HasRange(..), noRange)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.TypeChecking.Datatypes (isDataOrRecordType, DataOrRecord(..))
import Agda.TypeChecking.Records
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (primInf, CoinductionKit(..), coinductionKit)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Permutation as Perm
import Agda.Utils.SemiRing
import Agda.Utils.Singleton
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

type Graph n e = Graph.Graph n n e

-- | Check that the datatypes in the mutual block containing the given
--   declarations are strictly positive.
--
--   Also add information about positivity and recursivity of records
--   to the signature.
checkStrictlyPositive :: Info.MutualInfo -> Set QName -> TCM ()
checkStrictlyPositive mi qset = disableDestructiveUpdate $ do
  -- compute the occurrence graph for qs
  let qs = Set.toList qset
  reportSDoc "tc.pos.tick" 100 $ text "positivity of" <+> prettyTCM qs
  g <- buildOccurrenceGraph qset
  let (gstar, sccs') =
        Graph.gaussJordanFloydWarshallMcNaughtonYamada $ fmap occ g
  reportSDoc "tc.pos.tick" 100 $ text "constructed graph"
  reportSLn "tc.pos.graph" 5 $ "Positivity graph: N=" ++ show (size $ Graph.nodes g) ++
                               " E=" ++ show (length $ Graph.edges g)
  reportSDoc "tc.pos.graph" 10 $ vcat
    [ text "positivity graph for" <+> (fsep $ map prettyTCM qs)
    , nest 2 $ prettyTCM g
    ]
  reportSLn "tc.pos.graph" 5 $
    "Positivity graph (completed): E=" ++ show (length $ Graph.edges gstar)
  reportSDoc "tc.pos.graph" 50 $ vcat
    [ text "transitive closure of positivity graph for" <+>
      prettyTCM qs
    , nest 2 $ prettyTCM gstar
    ]

  -- remember argument occurrences for qs in the signature
  setArgOccs qset qs gstar
  reportSDoc "tc.pos.tick" 100 $ text "set args"

  -- check positivity for all strongly connected components of the graph for qs
  let sccs = map flattenSCC sccs'
  reportSDoc "tc.pos.graph.sccs" 10 $ do
    let (triv, others) = partitionEithers $ for sccs' $ \ scc -> case scc of
          AcyclicSCC v -> Left v
          CyclicSCC vs -> Right vs
    sep [ text $ show (length triv) ++ " trivial sccs"
        , text $ show (length others) ++ " non-trivial sccs with lengths " ++
            show (map length others)
        ]
  reportSDoc "tc.pos.graph.sccs" 15 $ text $ "  sccs = " ++ show sccs
  forM_ sccs $ \ scc -> setMut [ q | DefNode q <- scc ]
  mapM_ (checkPos g gstar) $ qs
  reportSDoc "tc.pos.tick" 100 $ text "checked positivity"

  where
    checkPos :: Graph Node Edge ->
                Graph Node Occurrence ->
                QName -> TCM ()
    checkPos g gstar q = inConcreteOrAbstractMode q $ \ _def -> do
      -- we check positivity only for data or record definitions
      whenJustM (isDatatype q) $ \ dr -> do
        reportSDoc "tc.pos.check" 10 $ text "Checking positivity of" <+> prettyTCM q

        let loop :: Maybe Occurrence
            loop = Graph.lookup (DefNode q) (DefNode q) gstar

            -- Note the property
            -- Agda.Utils.Graph.AdjacencyMap.Unidirectional.Tests.prop_productOfEdgesInBoundedWalk,
            -- which relates productOfEdgesInBoundedWalk to
            -- gaussJordanFloydWarshallMcNaughtonYamada.

            reason bound =
              case productOfEdgesInBoundedWalk
                     occ g (DefNode q) (DefNode q) bound of
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
        when (Info.mutualPositivityCheck mi) $
          whenM positivityCheckEnabled $
            case loop of
            Just o | o <= JustPos ->
              warning $ NotStrictlyPositive q (reason JustPos)
            _ -> return ()

        -- if we find an unguarded record, mark it as such
        when (dr == IsRecord) $
          case loop of
            Just o | o <= StrictPos -> do
              reportSDoc "tc.pos.record" 5 $ how "not guarded" StrictPos
              unguardedRecord q
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
                text "record type " <+> prettyTCM q <+>
                text "is not recursive"
              nonRecursiveRecord q
            _ -> return ()

    checkInduction :: QName -> TCM ()
    checkInduction q =
      -- ASR (01 January 2016). We don't raise this error if the
      -- NO_POSITIVITY_CHECK pragma was set on in the record. See
      -- Issue 1760.
      when (Info.mutualPositivityCheck mi) $
        whenM positivityCheckEnabled $ do
        -- Check whether the recursive record has been declared as
        -- 'Inductive' or 'Coinductive'.  Otherwise, error.
        unlessM (isJust . recInduction . theDef <$> getConstInfo q) $
          setCurrentRange (nameBindingSite $ qnameName q) $
            typeError . GenericDocError =<<
              text "Recursive record" <+> prettyTCM q <+>
              text "needs to be declared as either inductive or coinductive"

    occ (Edge o _) = o

    isDatatype :: QName -> TCM (Maybe DataOrRecord)
    isDatatype q = do
      def <- theDef <$> getConstInfo q
      return $ case def of
        Datatype{dataClause = Nothing} -> Just IsData
        Record  {recClause  = Nothing} -> Just IsRecord
        _ -> Nothing

    -- Set the mutually recursive identifiers for a SCC.
    setMut :: [QName] -> TCM ()
    setMut []  = return ()  -- nothing to do
    setMut [q] = return ()  -- no mutual recursion
    setMut qs  = forM_ qs $ \ q -> setMutual q (delete q qs)
      -- TODO: The previous line is at least quadratic in the length
      -- of qs (assuming that the expression "delete q qs" is always
      -- forced, for instance due to serialisation). Presumably qs is
      -- usually short, but in some cases (for instance for generated
      -- code) it may be long. Wouldn't it be better to assign a
      -- unique identifier to each SCC, and avoid storing lists?

    -- Set the polarity of the arguments to a couple of definitions
    setArgOccs :: Set QName -> [QName] -> Graph Node Occurrence -> TCM ()
    setArgOccs qset qs g = do
      -- Compute a map from each name in q to the maximal argument index
      let maxs = Map.fromListWith max
           [ (q, i) | ArgNode q i <- Set.toList $ Graph.sourceNodes g, q `Set.member` qset ]
      forM_ qs $ \ q -> inConcreteOrAbstractMode q $ \ def -> do
        reportSDoc "tc.pos.args" 10 $ text "checking args of" <+> prettyTCM q
        n <- getDefArity def
        -- If there is no outgoing edge @ArgNode q i@, all @n@ arguments are @Unused@.
        -- Otherwise, we obtain the occurrences from the Graph.
        let findOcc i = fromMaybe Unused $ Graph.lookup (ArgNode q i) (DefNode q) g
            args = caseMaybe (Map.lookup q maxs) (replicate n Unused) $ \ m ->
              map findOcc [0 .. max m (n - 1)]
        reportSDoc "tc.pos.args" 10 $ sep
          [ text "args of" <+> prettyTCM q <+> text "="
          , nest 2 $ prettyList $ map (text . show) args
          ]
        -- The list args can take a long time to compute, but contains
        -- small elements, and is stored in the interface (right?), so
        -- it is computed deep-strictly.
        setArgOccurrences q $!! args

getDefArity :: Definition -> TCM Int
getDefArity def = case theDef def of
  defn@Function{} -> do
    let dropped = projectionArgs defn
    -- TODO: instantiateFull followed by arity could perhaps be
    -- optimised, presumably the instantiation can be performed
    -- lazily.
    subtract dropped . arity <$> instantiateFull (defType def)
  Datatype{ dataPars = n } -> return n
  Record{ recPars = n }    -> return n
  _                        -> return 0

-- Operations on occurrences -------------------------------------------

-- See also Agda.TypeChecking.Positivity.Occurrence.

(>*<) :: OccursWhere -> OccursWhere -> OccursWhere
Unknown      >*< _            = Unknown
Known _    _ >*< Unknown      = Unknown
Known r1 os1 >*< Known r2 os2 = Known (fuseRange r1 r2) (os1 DS.>< os2)

instance PrettyTCM OccursWhere where
  prettyTCM o = prettyOs $ map maxOneLeftOfArrow $ uniq $ splitOnDef o
    where
      nth 0 = pwords "first"
      nth 1 = pwords "second"
      nth 2 = pwords "third"
      nth n = pwords $ show (n + 1) ++ "th"

      -- remove consecutive duplicates
      uniq = map head . group

      prettyOs [] = __IMPOSSIBLE__
      prettyOs [o] = prettyO o <> text "."
      prettyOs (o:os) = prettyO o <> text ", which occurs" $$ prettyOs os

      prettyO Unknown      = empty
      prettyO (Known _ ws) =
        Fold.foldrM (\w d -> return d $$ fsep (prettyW w)) empty ws

      prettyW w = case w of
        LeftOfArrow  -> pwords "to the left of an arrow"
        DefArg q i   -> pwords "in the" ++ nth i ++ pwords "argument to" ++
                          [prettyTCM q]
        UnderInf     -> pwords "under" ++
                        [do -- this cannot fail if an 'UnderInf' has been generated
                            Def inf _ <- ignoreSharing <$> primInf
                            prettyTCM inf]
        VarArg       -> pwords "in an argument to a bound variable"
        MetaArg      -> pwords "in an argument to a metavariable"
        ConArgType c -> pwords "in the type of the constructor" ++ [prettyTCM c]
        IndArgType c -> pwords "in an index of the target type of the constructor" ++ [prettyTCM c]
        InClause i   -> pwords "in the" ++ nth i ++ pwords "clause"
        Matched      -> pwords "as matched against"
        InDefOf d    -> pwords "in the definition of" ++ [prettyTCM d]

      maxOneLeftOfArrow Unknown      = Unknown
      maxOneLeftOfArrow (Known r ws) = Known r $
        noArrows
          DS.><
        case DS.viewl startsWithArrow of
          DS.EmptyL  -> DS.empty
          w DS.:< ws -> w DS.<| DS.filter (not . isArrow) ws
        where
        (noArrows, startsWithArrow) = DS.breakl isArrow ws

        isArrow LeftOfArrow{} = True
        isArrow _             = False

      splitOnDef Unknown      = [Unknown]
      splitOnDef (Known r ws) = split ws DS.empty
        where
        split ws acc = case DS.viewl ws of
          w@InDefOf{} DS.:< ws -> let rest = split ws (DS.singleton w) in
                                  if DS.null acc
                                  then rest
                                  else Known r acc : rest
          w           DS.:< ws -> split ws (acc DS.|> w)
          DS.EmptyL            -> [Known r acc]

instance Sized OccursWhere where
  size Unknown      = 1
  size (Known _ ws) = 1 + size ws

-- Computing occurrences --------------------------------------------------

data Item = AnArg Nat
          | ADef QName
  deriving (Eq, Ord, Show)

instance HasRange Item where
  getRange (AnArg _) = noRange
  getRange (ADef qn)   = getRange qn

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
  | OccursHere' Item OccursWhere

emptyOB :: OccurrencesBuilder
emptyOB = Concat []

(>+<) :: OccurrencesBuilder -> OccurrencesBuilder -> OccurrencesBuilder
occs1 >+< occs2 = Concat [occs1, occs2]

-- | Removes 'OnlyVarsUpTo' entries and adds 'OccursWhere' entries.
--
-- WARNING: There can be lots of sharing between the generated
-- 'OccursWhere' entries. Traversing all of these entries could be
-- expensive. (See 'computeEdges' for an example.)
preprocess :: OccurrencesBuilder -> OccurrencesBuilder'
preprocess ob = case pp Nothing DS.empty ob of
  Nothing -> Concat' []
  Just ob -> ob
  where
  pp :: Maybe Nat
        -- ^ Variables larger than or equal to this number, if any,
        --   are not retained.
     -> DS.Seq Where
     -> OccurrencesBuilder
     -> Maybe OccurrencesBuilder'
  pp !m ws (Concat obs)        = case catMaybes $ map (pp m ws) obs of
                                   []  -> Nothing
                                   obs -> return (Concat' obs)
  pp  m ws (OccursAs w ob)     = OccursAs' w <$> pp m (ws DS.|> w) ob
  pp  m ws (OnlyVarsUpTo n ob) = pp (Just $! maybe n (min n) m) ws ob
  pp  m ws (OccursHere i)      = do guard keep
                                    return (OccursHere' i (Known (getRange i) ws))
    where
    keep = case (m, i) of
      (Nothing, _)      -> True
      (_, ADef _)       -> True
      (Just m, AnArg i) -> i < m

-- | A type used locally in 'flatten'.
data OccursWheres
  = OccursWheres :++ OccursWheres
  | Occurs OccursWhere

-- | An interpreter for 'OccurrencesBuilder'.
--
-- WARNING: There can be lots of sharing between the generated
-- 'OccursWhere' entries. Traversing all of these entries could be
-- expensive. (See 'computeEdges' for an example.)
flatten :: OccurrencesBuilder -> Occurrences
flatten =
  fmap (flip flatten'' []) .
  Map.fromListWith (:++) .
  flip flatten' [] .
  preprocess
  where
  flatten' :: OccurrencesBuilder'
           -> [(Item, OccursWheres)] -> [(Item, OccursWheres)]
  flatten' (Concat' obs)     = foldr (\occs f -> flatten' occs . f) id obs
  flatten' (OccursAs' _ ob)  = flatten' ob
  flatten' (OccursHere' i o) = ((i, Occurs o) :)

  flatten'' (os1 :++ os2) = flatten'' os1 . flatten'' os2
  flatten'' (Occurs o)    = (o :)

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

withExtendedOccEnv :: Maybe Item -> OccM a -> OccM a
withExtendedOccEnv i = withExtendedOccEnv' [i]

withExtendedOccEnv' :: [Maybe Item] -> OccM a -> OccM a
withExtendedOccEnv' is = local $ \ e -> e { vars = is ++ vars e }

-- | Running the monad
getOccurrences
  :: (Show a, PrettyTCM a, ComputeOccurrences a)
  => [Maybe Item] -> a -> TCM OccurrencesBuilder
getOccurrences vars a = do
  reportSDoc "tc.pos.occ" 70 $ text "computing occurrences in " <+> text (show a)
  reportSDoc "tc.pos.occ" 20 $ text "computing occurrences in " <+> prettyTCM a
  kit <- coinductionKit
  return $ runReader (occurrences a) $ OccEnv vars $ fmap nameOfInf kit

class ComputeOccurrences a where
  occurrences :: a -> OccM OccurrencesBuilder

instance ComputeOccurrences Clause where
  occurrences cl = do
    let ps    = namedClausePats cl
        items = IntMap.elems $ patItems ps -- sorted from low to high DBI
    (Concat (mapMaybe matching (zip [0..] ps)) >+<) <$>
      withExtendedOccEnv' items (occurrences $ clauseBody cl)
    where
      matching (i, p)
        | properlyMatching (namedThing $ unArg p) =
            Just $ OccursAs Matched $ OccursHere $ AnArg i
        | otherwise                  = Nothing

      -- @patItems ps@ creates a map from the pattern variables of @ps@
      -- to the index of the argument they are bound in.
      patItems ps = mconcat $ zipWith patItem [0..] ps

      -- @patItem i p@ assigns index @i@ to each pattern variable in @p@
      patItem :: Int -> NamedArg DeBruijnPattern -> IntMap (Maybe Item)
      patItem i p = Fold.foldMap makeEntry ixs
        where
          ixs = map dbPatVarIndex $ lefts $ map unArg $ patternVars $ namedThing <$> p

          makeEntry x = singleton (x, Just $ AnArg i)

instance ComputeOccurrences Term where
  occurrences v = case unSpine v of
    Var i args -> do
      vars <- asks vars
      occs <- occurrences args
      -- Apparently some development version of GHC chokes if the
      -- following line is replaced by vars ! i.
      let mi | i < length vars = vars !! i
             | otherwise       = flip trace __IMPOSSIBLE__ $
                 "impossible: occurrence of de Bruijn index " ++ show i ++
                 " in vars " ++ show vars ++ " is unbound"
      return $ maybe emptyOB OccursHere mi >+< OccursAs VarArg occs

    Def d args   -> do
      inf <- asks inf
      let occsAs = if Just d /= inf then OccursAs . DefArg d else \ n ->
            -- the principal argument of builtin INF (∞) is the second (n==1)
            -- the first is a level argument (n==0, counting from 0!)
            if n == 1 then OccursAs UnderInf else OccursAs (DefArg d n)
      occs <- mapM occurrences args
      return $ OccursHere (ADef d) >+< Concat (zipWith occsAs [0..] occs)
    Con c args   -> occurrences args
    MetaV _ args -> OccursAs MetaArg <$> occurrences args
    Pi a b       -> do
      oa <- occurrences a
      ob <- occurrences b
      return $ OccursAs LeftOfArrow oa >+< ob
    Lam _ b      -> occurrences b
    Level l      -> occurrences l
    Lit{}        -> return emptyOB
    Sort{}       -> return emptyOB
    DontCare _   -> return emptyOB -- Andreas, 2011-09-09: do we need to check for negative occurrences in irrelevant positions?
    Shared p     -> occurrences $ derefPtr p

instance ComputeOccurrences Level where
  occurrences (Max as) = occurrences as

instance ComputeOccurrences PlusLevel where
  occurrences ClosedLevel{} = return emptyOB
  occurrences (Plus _ l)    = occurrences l

instance ComputeOccurrences LevelAtom where
  occurrences l = case l of
    MetaLevel x es   -> occurrences $ MetaV x es
      -- Andreas, 2016-07-25, issue 2108
      -- NOT: OccursAs MetaArg <$> occurrences vs
      -- since we need to unSpine!
      -- (Otherwise, we run into __IMPOSSIBLE__ at Proj elims)
    BlockedLevel _ v -> occurrences v
    NeutralLevel _ v -> occurrences v
    UnreducedLevel v -> occurrences v

instance ComputeOccurrences Type where
  occurrences (El _ v) = occurrences v

instance ComputeOccurrences a => ComputeOccurrences (Tele a) where
  occurrences EmptyTel        = return emptyOB
  occurrences (ExtendTel a b) = occurrences (a, b)

instance ComputeOccurrences a => ComputeOccurrences (Abs a) where
  occurrences (Abs   _ b) = withExtendedOccEnv Nothing $ occurrences b
  occurrences (NoAbs _ b) = occurrences b

instance ComputeOccurrences a => ComputeOccurrences (Elim' a) where
  occurrences Proj{}    = __IMPOSSIBLE__
  occurrences (Apply a) = occurrences a

instance ComputeOccurrences a => ComputeOccurrences (Arg a) where
  occurrences = occurrences . unArg

instance ComputeOccurrences a => ComputeOccurrences (Dom a) where
  occurrences = occurrences . unDom

instance ComputeOccurrences a => ComputeOccurrences [a] where
  occurrences vs = Concat <$> mapM occurrences vs

instance ComputeOccurrences a => ComputeOccurrences (Maybe a) where
  occurrences (Just v) = occurrences v
  occurrences Nothing  = return emptyOB

instance (ComputeOccurrences a, ComputeOccurrences b) => ComputeOccurrences (a, b) where
  occurrences (x, y) = do
    ox <- occurrences x
    oy <- occurrences y
    return $ ox >+< oy

-- | Computes the occurrences in the given definition.
--
-- WARNING: There can be lots of sharing between the 'OccursWhere'
-- entries. Traversing all of these entries could be expensive. (See
-- 'computeEdges' for an example.)
computeOccurrences :: QName -> TCM Occurrences
computeOccurrences q = flatten <$> computeOccurrences' q

-- | Computes the occurrences in the given definition.
computeOccurrences' :: QName -> TCM OccurrencesBuilder
computeOccurrences' q = inConcreteOrAbstractMode q $ \ def -> do
  reportSDoc "tc.pos" 25 $ do
    let a = defAbstract def
    m <- asks envAbstractMode
    cur <- asks envCurrentModule
    text "computeOccurrences" <+> prettyTCM q <+> text (show a) <+> text (show m)
      <+> prettyTCM cur
  OccursAs (InDefOf q) <$> case theDef def of
    Function{funClauses = cs} -> do
      n  <- getDefArity def
      cs <- map (etaExpandClause n) <$> instantiateFull cs
      Concat . zipWith (OccursAs . InClause) [0..] <$>
        mapM (getOccurrences []) cs
    Datatype{dataClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Datatype{dataPars = np, dataCons = cs}       -> do
      -- Andreas, 2013-02-27: first, each data index occurs as matched on.
      TelV tel t <- telView $ defType def
      let xs  = [np .. size tel - 1] -- argument positions corresponding to indices
          ioccs = Concat $ map (OccursAs Matched . OccursHere . AnArg) xs
      -- Then, we compute the occurrences in the constructor types.
      let conOcc c = do
            a <- defType <$> getConstInfo c
            TelV tel t <- telView' <$> normalise a -- normalization needed e.g. for test/succeed/Bush.agda
            let indices = case unEl t of
                            Def _ vs -> genericDrop np vs
                            _        -> __IMPOSSIBLE__
            let tel'    = telFromList $ genericDrop np $ telToList tel
                vars np = map (Just . AnArg) $ downFrom np
            (>+<) <$> (OccursAs (ConArgType c) <$> getOccurrences (vars np) tel')
                  <*> (OccursAs (IndArgType c) . OnlyVarsUpTo np <$> getOccurrences (vars $ size tel) indices)
      (>+<) ioccs <$> (Concat <$> mapM conOcc cs)
    Record{recClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Record{recPars = np, recTel = tel} -> do
      let tel' = telFromList $ genericDrop np $ telToList tel
          vars = map (Just . AnArg) $ downFrom np
      getOccurrences vars =<< instantiateFull tel'

    -- Arguments to other kinds of definitions are hard-wired.
    Constructor{} -> return emptyOB
    Axiom{}       -> return emptyOB
    Primitive{}   -> return emptyOB
    AbstractDefn  -> __IMPOSSIBLE__

-- | Eta expand a clause to have the given number of variables.
--   Warning: doesn't put correct types in telescope!
--   This is used instead of special treatment of lambdas
--   (which was unsound: issue 121)
etaExpandClause :: Nat -> Clause -> Clause
etaExpandClause n c
  | m <= 0    = c
  | otherwise = c
      { namedClausePats = raise m (namedClausePats c) ++
                          map (\i -> defaultArg $ namedDBVarP i underscore) (downFrom m)
      , clauseBody      = liftBody m $ clauseBody c
      , clauseTel       = telFromList $
          telToList (clauseTel c) ++ (replicate m $ (underscore,) <$> dummyDom)
          -- dummyDom, not __IMPOSSIBLE__, because of debug printing.
      }
  where
    m = n - genericLength (namedClausePats c)

    vars = map (defaultArg . var) $ downFrom m
--    vars = reverse [ defaultArg $ var i | i <- [0..m - 1] ]

    liftBody m (Just v) = Just $ raise m v `apply` vars
    liftBody m Nothing  = Nothing

-- Building the occurrence graph ------------------------------------------

data Node = DefNode !QName
          | ArgNode !QName !Nat
  deriving (Eq, Ord)

instance Show Node where
  show (DefNode q)   = show q
  show (ArgNode q i) = show q ++ "." ++ show i

instance PrettyTCM Node where
  prettyTCM (DefNode q)   = prettyTCM q
  prettyTCM (ArgNode q i) = prettyTCM q <> text ("." ++ show i)

instance PrettyTCM n => PrettyTCM (WithNode n Edge) where
  prettyTCM (WithNode n (Edge o w)) =
    prettyTCM o <+> prettyTCM n <+> fsep (pwords $ show w)

-- | Edge labels for the positivity graph.
data Edge = Edge !Occurrence OccursWhere
  deriving (Eq, Ord, Show)

instance Null Edge where
  null (Edge o _) = null o
  empty = Edge empty Unknown

-- | These operations form a semiring if we quotient by the relation
-- \"the 'Occurrence' components are equal\".

instance SemiRing Edge where
  ozero = Edge ozero Unknown
  oone  = Edge oone  Unknown

  oplus _                    e@(Edge Mixed _)     = e -- dominant
  oplus e@(Edge Mixed _) _                        = e
  oplus (Edge Unused _)      e                    = e -- neutral
  oplus e                    (Edge Unused _)      = e
  oplus (Edge JustNeg _)     e@(Edge JustNeg _)   = e
  oplus _                    e@(Edge JustNeg w)   = Edge Mixed w
  oplus e@(Edge JustNeg w)   _                    = Edge Mixed w
  oplus _                    e@(Edge JustPos _)   = e -- dominates strict pos.
  oplus e@(Edge JustPos _)   _                    = e
  oplus _                    e@(Edge StrictPos _) = e -- dominates 'GuardPos'
  oplus e@(Edge StrictPos _) _                    = e
  oplus (Edge GuardPos _)    e@(Edge GuardPos _)  = e

  otimes (Edge o1 w1) (Edge o2 w2) = Edge (otimes o1 o2) (w1 >*< w2)

-- | As 'OccursWhere' does not have an 'oplus' we cannot do something meaningful
--   for the @OccursWhere@ here.
--
--   E.g. @ostar (Edge JustNeg w) = Edge Mixed (w `oplus` (w >*< w))@
--   would probably more sense, if we could do it.
instance StarSemiRing Edge where
  ostar (Edge o w) = Edge (ostar o) w

-- | WARNING: There can be lots of sharing between the 'OccursWhere'
-- entries in the edges. Traversing all of these entries could be
-- expensive. (See 'computeEdges' for an example.)
buildOccurrenceGraph :: Set QName -> TCM (Graph Node Edge)
buildOccurrenceGraph qs =
  Graph.fromListWith oplus . concat <$>
    mapM defGraph (Set.toList qs)
  where
    defGraph :: QName -> TCM [Graph.Edge Node Node Edge]
    defGraph q = inConcreteOrAbstractMode q $ \ _def -> do
      occs <- computeOccurrences' q

      reportSDoc "tc.pos.occs" 40 $
        (text "Occurrences in" <+> prettyTCM q <> text ":")
          $+$
        (nest 2 $ vcat $
           map (\(i, (n, s)) ->
                   text (show i) <> text ":" <+> text (show n) <+>
                   text "occurrences, of total size" <+>
                   text (show s)) $
           sortBy (compare `on` fst . snd) $
           map (\(i, os) -> (i, (length os, sum $ map size os))) $
           Map.toList (flatten occs))
      reportSDoc "tc.pos.occs" 50 $
        (nest 2 $ vcat $
           map (\(i, os) ->
                   (text (show i) <> text ":")
                     $+$
                   (nest 2 $ vcat $ map (text . show) os))
               (Map.toList (flatten occs)))

      -- Placing this line before the reportSDoc lines above creates a
      -- space leak: occs is retained for too long.
      es <- computeEdges qs q occs

      reportSDoc "tc.pos.occs.edges" 60 $
        text "Edges:"
          $+$
        (nest 2 $ vcat $
           map (\e ->
                   let Edge o w = Graph.label e in
                   prettyTCM (Graph.source e) <+>
                   text "-[" <+> text (show o) <> text "," <+>
                                 text (show w) <+> text "]->" <+>
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
-- * @'Known' ('DS.fromList' ['InDefOf' "F", 'InClause' 0])@,
--
-- * @'Known' ('DS.fromList' ['InDefOf' "F", 'InClause' 0, 'LeftOfArrow'])@,
--
-- * @'Known' ('DS.fromList' ['InDefOf' "F", 'InClause' 0, 'LeftOfArrow', 'LeftOfArrow'])@,
--
-- * @'Known' ('DS.fromList' ['InDefOf' "F", 'InClause' 0, 'LeftOfArrow', 'LeftOfArrow', 'LeftOfArrow'])@,
--
-- * and so on.
computeEdges
  :: Set QName
     -- ^ The names in the current mutual block.
  -> QName
     -- ^ The current name.
  -> OccurrencesBuilder
  -> TCM [Graph.Edge Node Node Edge]
computeEdges muts q ob =
  ($ []) <$> mkEdge __IMPOSSIBLE__ StrictPos (preprocess ob)
  where
  mkEdge to !pol ob = case ob of
    Concat' obs     -> foldr (liftM2 (.)) (return id)
                         [ mkEdge to pol ob | ob <- obs ]
    OccursAs' w ob  -> do (to, pol) <- mkEdge' to pol w
                          mkEdge to pol ob
    OccursHere' i o -> return $
                         if null pol
                         then id
                         else (Graph.Edge
                                 { Graph.source = case i of
                                                    AnArg i -> ArgNode q i
                                                    ADef q  -> DefNode q
                                 , Graph.target = to
                                 , Graph.label  = Edge pol o
                                 } :)

  mkEdge' to !pol w = case w of
    VarArg         -> mixed
    MetaArg        -> mixed
    LeftOfArrow    -> negative
    DefArg d i     -> do
      pol' <- isGuarding d
      if Set.member d muts
        then return (ArgNode d i, pol')
        else addPol =<< otimes pol' <$> getArgOccurrence d i
    UnderInf       -> addPol GuardPos -- Andreas, 2012-06-09: ∞ is guarding
    ConArgType _   -> keepGoing
    IndArgType _   -> mixed
    InClause _     -> keepGoing
    Matched        -> mixed -- consider arguments matched against as used
    InDefOf d      -> do
      pol' <- isGuarding d
      return (DefNode d, pol')
    where
    keepGoing   = return (to, pol)
    mixed       = return (to, Mixed)
    negative    = return (to, otimes pol JustNeg)
    addPol pol' = return (to, otimes pol pol')

  isGuarding d = do
    isDR <- isDataOrRecordType d
    return $ case isDR of
      Just IsData -> GuardPos  -- a datatype is guarding
      _           -> StrictPos
