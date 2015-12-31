{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Check that a datatype is strictly positive.
module Agda.TypeChecking.Positivity where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Monad.Reader

import Data.Either
import Data.Graph (SCC(..), flattenSCC)
import Data.List as List hiding (null)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Debug.Trace

import Test.QuickCheck

import Agda.Syntax.Common
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.TypeChecking.Datatypes (isDataOrRecordType, DataOrRecord(..))
import Agda.TypeChecking.Records (unguardedRecord, recursiveRecord)
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
  -- remove @Unused@ edges
  g <- Graph.clean <$> buildOccurrenceGraph qset
  let gstar = Graph.gaussJordanFloydWarshallMcNaughtonYamada $ fmap occ g
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
  let sccs' = Graph.sccs' gstar
      sccs  = map flattenSCC sccs'
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
    checkPos g gstar q = inConcreteOrAbstractMode q $ do
      -- we check positivity only for data or record definitions
      whenJustM (isDatatype q) $ \ dr -> do
        reportSDoc "tc.pos.check" 10 $ text "Checking positivity of" <+> prettyTCM q

        let loop :: Maybe Occurrence
            loop = Graph.lookup (DefNode q) (DefNode q) gstar

            how :: String -> (Occurrence -> Bool) -> TCM Doc
            how msg p =
              fsep $ [prettyTCM q] ++ pwords "is" ++
                case filter (p . occ) $
                     -- Graph.allTrails (DefNode q) (DefNode q) g of -- exponential, see Issue 1612
                     Graph.allPaths (p . occ) (DefNode q) (DefNode q) g of
                  Edge _ how : _ -> pwords (msg ++ ", because it occurs") ++
                                    [prettyTCM how]
                  _              -> pwords $ msg ++ "."

                  -- For an example of code that exercises the latter,
                  -- uninformative clause above, see
                  -- test/fail/BadInductionRecursion5.agda. Note that
                  -- for this example the counterexample is not a
                  -- trail.

                  -- If a suitable StarSemiRing instance can be
                  -- defined for Edge, then
                  -- gaussJordanFloydWarshallMcNaughtonYamada can be
                  -- used instead of allTrails, thus avoiding the
                  -- uninformative clause.

        -- if we have a negative loop, raise error
        whenM positivityCheckEnabled $
          -- ASR (23 December 2015). We don't raise a strictly
          -- positive error if the NO_POSITIVITY_CHECK pragma was set
          -- on in the mutual block. See Issue 1614.
          if Info.mutualPositivityCheck mi
            then
              case loop of
              Just o | p o -> do
                err <- how "not strictly positive" p
                setCurrentRange q $ typeError $ GenericDocError err
                where p = (<= JustPos)
              _ -> return ()
            else return ()

        -- if we find an unguarded record, mark it as such
        when (dr == IsRecord) $
          case loop of
            Just o | p o -> do
              reportSDoc "tc.pos.record" 5 $ how "not guarded" p
              unguardedRecord q
              checkInduction q
              where p = (<= StrictPos)
            _ ->
              -- otherwise, if the record is recursive, mark it as well
              case loop of
                Just o | p o -> do
                  reportSDoc "tc.pos.record" 5 $ how "recursive" p
                  recursiveRecord q
                  checkInduction q
                  where p = (== GuardPos)
                _ -> return ()

    checkInduction :: QName -> TCM ()
    checkInduction q = whenM positivityCheckEnabled $ do
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

    -- Set the polarity of the arguments to a couple of definitions
    setArgOccs :: Set QName -> [QName] -> Graph Node Occurrence -> TCM ()
    setArgOccs qset qs g = do
      -- Compute a map from each name in q to the maximal argument index
      let maxs = Map.fromListWith max
           [ (q, i) | ArgNode q i <- Set.toList $ Graph.sourceNodes g, q `Set.member` qset ]
      forM_ qs $ \ q -> inConcreteOrAbstractMode q $ do
        reportSDoc "tc.pos.args" 10 $ text "checking args of" <+> prettyTCM q
        n <- getDefArity =<< getConstInfo q
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
    subtract dropped . arity <$> instantiateFull (defType def)
  Datatype{ dataPars = n } -> return n
  Record{ recPars = n }    -> return n
  _                        -> return 0

-- Specification of occurrences -------------------------------------------

-- See also Agda.TypeChecking.Positivity.Occurrence.

-- | Description of an occurrence.
data OccursWhere
  = LeftOfArrow OccursWhere
  | DefArg QName Nat OccursWhere -- ^ in the nth argument of a define constant
  | UnderInf OccursWhere         -- ^ in the principal argument of built-in ∞
  | VarArg OccursWhere           -- ^ as an argument to a bound variable
  | MetaArg OccursWhere          -- ^ as an argument of a metavariable
  | ConArgType QName OccursWhere -- ^ in the type of a constructor
  | IndArgType QName OccursWhere -- ^ in a datatype index of a constructor
  | InClause Nat OccursWhere     -- ^ in the nth clause of a defined function
  | Matched OccursWhere          -- ^ matched against in a clause of a defined function
  | InDefOf QName OccursWhere    -- ^ in the definition of a constant
  | Here
  | Unknown                      -- ^ an unknown position (treated as negative)
  deriving (Show, Eq, Ord)

(>*<) :: OccursWhere -> OccursWhere -> OccursWhere
Here            >*< o  = o
Unknown         >*< o  = Unknown
LeftOfArrow o1  >*< o2 = LeftOfArrow (o1 >*< o2)
DefArg d i o1   >*< o2 = DefArg d i (o1 >*< o2)
UnderInf o1     >*< o2 = UnderInf (o1 >*< o2)
VarArg o1       >*< o2 = VarArg (o1 >*< o2)
MetaArg o1      >*< o2 = MetaArg (o1 >*< o2)
ConArgType c o1 >*< o2 = ConArgType c (o1 >*< o2)
IndArgType c o1 >*< o2 = IndArgType c (o1 >*< o2)
InClause i o1   >*< o2 = InClause i (o1 >*< o2)
Matched o1      >*< o2 = Matched (o1 >*< o2)
InDefOf d o1    >*< o2 = InDefOf d (o1 >*< o2)

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

      prettyO o = case o of
        Here           -> empty
        Unknown        -> empty
        LeftOfArrow o  -> explain o $ pwords "to the left of an arrow"
        DefArg q i o   -> explain o $ pwords "in the" ++ nth i ++ pwords "argument to" ++
                                      [prettyTCM q]
        UnderInf o     -> do
          Def inf _ <- ignoreSharing <$> primInf  -- this cannot fail if an 'UnderInf' has been generated
          explain o $ pwords "under" ++ [prettyTCM inf]
        VarArg o       -> explain o $ pwords "in an argument to a bound variable"
        MetaArg o      -> explain o $ pwords "in an argument to a metavariable"
        ConArgType c o -> explain o $ pwords "in the type of the constructor" ++ [prettyTCM c]
        IndArgType c o -> explain o $ pwords "in an index of the target type of the constructor" ++ [prettyTCM c]
        InClause i o   -> explain o $ pwords "in the" ++ nth i ++ pwords "clause"
        Matched o      -> explain o $ pwords "as matched against"
        InDefOf d o    -> explain o $ pwords "in the definition of" ++ [prettyTCM d]

      explain o ds = prettyO o $$ fsep ds

      maxOneLeftOfArrow o = case o of
        LeftOfArrow o  -> LeftOfArrow $ purgeArrows o
        Here           -> Here
        Unknown        -> Unknown
        DefArg q i o   -> DefArg q i   $ maxOneLeftOfArrow o
        UnderInf o     -> UnderInf     $ maxOneLeftOfArrow o
        InDefOf d o    -> InDefOf d    $ maxOneLeftOfArrow o
        VarArg o       -> VarArg       $ maxOneLeftOfArrow o
        MetaArg o      -> MetaArg      $ maxOneLeftOfArrow o
        ConArgType c o -> ConArgType c $ maxOneLeftOfArrow o
        IndArgType c o -> IndArgType c $ maxOneLeftOfArrow o
        InClause i o   -> InClause i   $ maxOneLeftOfArrow o
        Matched o      -> Matched      $ maxOneLeftOfArrow o

      purgeArrows o = case o of
        LeftOfArrow o -> purgeArrows o
        Here           -> Here
        Unknown        -> Unknown
        DefArg q i o   -> DefArg q i   $ purgeArrows o
        UnderInf o     -> UnderInf     $ purgeArrows o
        InDefOf d o    -> InDefOf d    $ purgeArrows o
        VarArg o       -> VarArg       $ purgeArrows o
        MetaArg o      -> MetaArg      $ purgeArrows o
        ConArgType c o -> ConArgType c $ purgeArrows o
        IndArgType c o -> IndArgType c $ purgeArrows o
        InClause i o   -> InClause i   $ purgeArrows o
        Matched o      -> Matched      $ purgeArrows o

      splitOnDef o = case o of
        Here           -> [Here]
        Unknown        -> [Unknown]
        InDefOf d o    -> sp (InDefOf d) o
        LeftOfArrow o  -> sp LeftOfArrow o
        DefArg q i o   -> sp (DefArg q i) o
        UnderInf o     -> sp UnderInf o
        VarArg o       -> sp VarArg o
        MetaArg o      -> sp MetaArg o
        ConArgType c o -> sp (ConArgType c) o
        IndArgType c o -> sp (IndArgType c) o
        InClause i o   -> sp (InClause i) o
        Matched o      -> sp Matched o
        where
          sp f o = case splitOnDef o of
            os@(InDefOf _ _:_) -> f Here : os
            o:os               -> f o : os
            []                 -> __IMPOSSIBLE__

-- Computing occurrences --------------------------------------------------

data Item = AnArg Nat
          | ADef QName
  deriving (Eq, Ord, Show)

type Occurrences = Map Item [OccursWhere]

(>+<) :: Occurrences -> Occurrences -> Occurrences
(>+<) = Map.unionWith (++)

concatOccurs :: [Occurrences] -> Occurrences
concatOccurs = Map.unionsWith (++)

occursAs :: (OccursWhere -> OccursWhere) -> Occurrences -> Occurrences
occursAs f = Map.map (map f)

here :: Item -> Occurrences
here i = Map.singleton i [Here]

-- | @onlyVarsUpTo n occs@ discards occurrences of de Bruijn index @>= n@.
onlyVarsUpTo :: Nat -> Occurrences -> Occurrences
onlyVarsUpTo n = Map.filterWithKey p
  where p (AnArg i) v = i < n
        p (ADef q)  v = True

-- | Context for computing occurrences.
data OccEnv = OccEnv
  { vars :: [Maybe Item] -- ^ Items corresponding to the free variables.
  , inf  :: Maybe QName  -- ^ Name for ∞ builtin.
  }

-- | Monad for computing occurrences.
type OccM = Reader OccEnv

withExtendedOccEnv :: Maybe Item -> OccM a -> OccM a
withExtendedOccEnv i = local $ \ e -> e { vars = i : vars e }

-- | Running the monad
getOccurrences
  :: (Show a, PrettyTCM a, ComputeOccurrences a)
  => [Maybe Item] -> a -> TCM Occurrences
getOccurrences vars a = do
  reportSDoc "tc.pos.occ" 70 $ text "computing occurrences in " <+> text (show a)
  reportSDoc "tc.pos.occ" 20 $ text "computing occurrences in " <+> prettyTCM a
  kit <- coinductionKit
  return $ runReader (occurrences a) $ OccEnv vars $ fmap nameOfInf kit

class ComputeOccurrences a where
  occurrences :: a -> OccM Occurrences

instance ComputeOccurrences Clause where
  occurrences cl = do
    let ps = unnumberPatVars $ clausePats cl
    (concatOccurs (mapMaybe matching (zip [0..] ps)) >+<) <$>
      walk (patItems ps) (clauseBody cl)
    where
      matching (i, p)
        | properlyMatching (unArg p) = Just $ occursAs Matched $ here $ AnArg i
        | otherwise                  = Nothing

      walk _         NoBody     = return empty
      walk []        (Body v)   = occurrences v
      walk (i : pis) (Bind b)   = withExtendedOccEnv i $ walk pis $ absBody b
      walk []        Bind{}     = __IMPOSSIBLE__
      walk (_ : _)   Body{}     = __IMPOSSIBLE__

      -- @patItems ps@ creates a map from the pattern variables of @ps@
      -- to the index of the argument they are bound in.
      -- This map is given as a list.
      patItems ps = concat $ zipWith patItem [0..] ps

      -- @patItem i p@ replicates index @i@ as often as there are
      -- pattern variables in @p@ (dot patterns count as variable)
      patItem :: Int -> Arg Pattern -> [Maybe Item]
      patItem i p = map (const $ Just $ AnArg i) $ patternVars p

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
      return $ maybe empty here mi >+< occursAs VarArg occs

    Def d args   -> do
      inf <- asks inf
      let occsAs = if Just d /= inf then occursAs . DefArg d else \ n ->
            -- the principal argument of builtin INF (∞) is the second (n==1)
            -- the first is a level argument (n==0, counting from 0!)
            if n == 1 then occursAs UnderInf else occursAs (DefArg d n)
      occs <- mapM occurrences args
      return $ here (ADef d) >+< concatOccurs (zipWith occsAs [0..] occs)
    Con c args   -> occurrences args
    MetaV _ args -> occursAs MetaArg <$> occurrences args
    Pi a b       -> do
      oa <- occurrences a
      ob <- occurrences b
      return $ occursAs LeftOfArrow oa >+< ob
    Lam _ b      -> occurrences b
    Level l      -> occurrences l
    Lit{}        -> return empty
    Sort{}       -> return empty
    DontCare _   -> return empty -- Andreas, 2011-09-09: do we need to check for negative occurrences in irrelevant positions?
    Shared p     -> occurrences $ derefPtr p

instance ComputeOccurrences Level where
  occurrences (Max as) = occurrences as

instance ComputeOccurrences PlusLevel where
  occurrences ClosedLevel{} = return empty
  occurrences (Plus _ l)    = occurrences l

instance ComputeOccurrences LevelAtom where
  occurrences l = case l of
    MetaLevel _ vs   -> occursAs MetaArg <$> occurrences vs
    BlockedLevel _ v -> occurrences v
    NeutralLevel _ v -> occurrences v
    UnreducedLevel v -> occurrences v

instance ComputeOccurrences Type where
  occurrences (El _ v) = occurrences v

instance ComputeOccurrences a => ComputeOccurrences (Tele a) where
  occurrences EmptyTel        = return empty
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
  occurrences vs = concatOccurs <$> mapM occurrences vs

instance (ComputeOccurrences a, ComputeOccurrences b) => ComputeOccurrences (a, b) where
  occurrences (x, y) = do
    ox <- occurrences x
    oy <- occurrences y
    return $ ox >+< oy

-- | Compute the occurrences in a given definition.
computeOccurrences :: QName -> TCM Occurrences
computeOccurrences q = inConcreteOrAbstractMode q $ do
  reportSDoc "tc.pos" 25 $ do
    a <- defAbstract <$> getConstInfo q
    m <- asks envAbstractMode
    text "computeOccurrences" <+> prettyTCM q <+> text (show a) <+> text (show m)
  def <- getConstInfo q
  occursAs (InDefOf q) <$> case theDef def of
    Function{funClauses = cs} -> do
      n  <- getDefArity def
      cs <- map (etaExpandClause n) <$> instantiateFull cs
      concatOccurs . zipWith (occursAs . InClause) [0..] <$>
        mapM (getOccurrences []) cs
    Datatype{dataClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Datatype{dataPars = np, dataCons = cs}       -> do
      -- Andreas, 2013-02-27: first, each data index occurs as matched on.
      TelV tel t <- telView $ defType def
      let xs  = [np .. size tel - 1] -- argument positions corresponding to indices
          ioccs = concatOccurs $ map (occursAs Matched . here . AnArg) xs
      -- Then, we compute the occurrences in the constructor types.
      let conOcc c = do
            a <- defType <$> getConstInfo c
            TelV tel t <- telView' <$> normalise a -- normalization needed e.g. for test/succeed/Bush.agda
            let indices = case unEl t of
                            Def _ vs -> genericDrop np vs
                            _        -> __IMPOSSIBLE__
            let tel'    = telFromList $ genericDrop np $ telToList tel
                vars np = map (Just . AnArg) $ downFrom np
            (>+<) <$> (occursAs (ConArgType c) <$> getOccurrences (vars np) tel')
                  <*> (occursAs (IndArgType c) . onlyVarsUpTo np <$> getOccurrences (vars $ size tel) indices)
      (>+<) ioccs <$> (concatOccurs <$> mapM conOcc cs)
    Record{recClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Record{recPars = np, recTel = tel} -> do
      let tel' = telFromList $ genericDrop np $ telToList tel
          vars = map (Just . AnArg) $ downFrom np
      getOccurrences vars =<< instantiateFull tel'

    -- Arguments to other kinds of definitions are hard-wired.
    Constructor{} -> return empty
    Axiom{}       -> return empty
    Primitive{}   -> return empty

-- | Eta expand a clause to have the given number of variables.
--   Warning: doesn't put correct types in telescope!
--   This is used instead of special treatment of lambdas
--   (which was unsound: issue 121)
etaExpandClause :: Nat -> Clause -> Clause
etaExpandClause n c@Clause{ clauseTel = tel, namedClausePats = ps, clauseBody = b }
  | m <= 0    = c
  | otherwise = c
      { namedClausePats = raise m ps ++ map (defaultArg . unnamed . VarP . (,underscore)) (downFrom m)
      , clauseBody      = liftBody m b
      , clauseTel       = telFromList $
          telToList tel ++ (replicate m $ (underscore,) <$> dummyDom)
          -- dummyDom, not __IMPOSSIBLE__, because of debug printing.
      }
  where
    m = n - genericLength ps

    bind 0 = id
    bind n = Bind . Abs underscore . bind (n - 1)

    vars = map (defaultArg . var) $ downFrom m
--    vars = reverse [ defaultArg $ var i | i <- [0..m - 1] ]

    liftBody m (Bind b)   = Bind $ fmap (liftBody m) b
    liftBody m NoBody     = bind m NoBody
    liftBody m (Body v)   = bind m $ Body $ raise m v `apply` vars

-- Building the occurrence graph ------------------------------------------

data Node = DefNode QName
          | ArgNode QName Nat
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
data Edge = Edge Occurrence OccursWhere
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

buildOccurrenceGraph :: Set QName -> TCM (Graph Node Edge)
buildOccurrenceGraph qs = Graph.unionsWith oplus <$> mapM defGraph (Set.toList qs)
  where
    defGraph :: QName -> TCM (Graph Node Edge)
    defGraph q = do
      occs <- computeOccurrences q
      Graph.unionsWith oplus <$> do
        forM (Map.assocs occs) $ \ (item, occs) -> do
          let src = itemToNode item
          es <- mapM (computeEdge qs) occs
          return $ Graph.unionsWith oplus $
            for es $ \ (tgt, w) -> Graph.singleton src tgt w
      where
        itemToNode (AnArg i) = ArgNode q i
        itemToNode (ADef q)  = DefNode q

-- | Given an 'OccursWhere' computes the target node and an 'Edge'. The first
--   argument is the set of names in the current mutual block.
computeEdge :: Set QName -> OccursWhere -> TCM (Node, Edge)
computeEdge muts o = do
  (to, occ) <- mkEdge __IMPOSSIBLE__ StrictPos o
  return (to, Edge occ o)
  where
    mkEdge to pol o = case o of
      Here           -> return (to, pol)
      Unknown        -> return (to, Mixed)
      VarArg o       -> mixed o
      MetaArg o      -> mixed o
      LeftOfArrow o  -> negative o
      DefArg d i o   -> do
        isDR <- isDataOrRecordType d
        let pol' | isDR == Just IsData = GuardPos  -- a datatype is guarding
                 | otherwise           = StrictPos
        if Set.member d muts then mkEdge (ArgNode d i) pol' o
         else addPol o =<< otimes pol' <$> getArgOccurrence d i
{-
      DefArg d i o
        | Set.member d muts -> inArg d i o
        | otherwise         -> addPol o =<< getArgOccurrence d i
-}
      UnderInf o     -> addPol o GuardPos -- Andreas, 2012-06-09: ∞ is guarding
      ConArgType _ o -> keepGoing o
      IndArgType _ o -> mixed o
      InClause _ o   -> keepGoing o
      Matched o      -> mixed o -- consider arguments matched against as used
      InDefOf d o    -> do
        isDR <- isDataOrRecordType d
        let pol' | isDR == Just IsData = GuardPos  -- a datatype is guarding
                 | otherwise           = StrictPos
        mkEdge (DefNode d) pol' o
      where
        keepGoing     = mkEdge to pol
        mixed         = mkEdge to Mixed
        negative o    = mkEdge to (otimes pol JustNeg) o
        addPol o pol' = mkEdge to (otimes pol pol') o

        -- Reset polarity when changing the target node
        -- D: (A B -> C) generates a positive edge B --> A.1
        -- even though the context is negative.
        inArg d i = mkEdge (ArgNode d i) StrictPos

------------------------------------------------------------------------
-- * Generators and tests
------------------------------------------------------------------------

instance Arbitrary OccursWhere where
  arbitrary = sized arbitraryS
    where
    arbitraryS n = oneof $
      [ return Here
      , return Unknown
      ] ++
      if n <= 0 then [] else
        [ LeftOfArrow <$> arb
        , DefArg <$> arbitrary <*> arbitrary <*> arb
        , UnderInf <$> arb
        , VarArg <$> arb
        , MetaArg <$> arb
        , ConArgType <$> arbitrary <*> arb
        , IndArgType <$> arbitrary <*> arb
        , InClause <$> arbitrary <*> arb
        , Matched <$> arb
        , InDefOf <$> arbitrary <*> arb
        ]
      where arb = arbitraryS (n - 1)

  shrink x = replaceConstructor x ++ genericShrink x
    where
    replaceConstructor Here    = []
    replaceConstructor Unknown = []
    replaceConstructor _       = [Here, Unknown]

    genericShrink (LeftOfArrow a)  = a : [ LeftOfArrow a  | a <- shrink a ]
    genericShrink (DefArg a b c)   = c : [ DefArg a b c   | c <- shrink c ]
    genericShrink (UnderInf a)     = a : [ UnderInf a     | a <- shrink a ]
    genericShrink (VarArg a)       = a : [ VarArg a       | a <- shrink a ]
    genericShrink (MetaArg a)      = a : [ MetaArg a      | a <- shrink a ]
    genericShrink (ConArgType a b) = b : [ ConArgType a b | b <- shrink b ]
    genericShrink (IndArgType a b) = b : [ IndArgType a b | b <- shrink b ]
    genericShrink (InClause a b)   = b : [ InClause a b   | b <- shrink b ]
    genericShrink (Matched a)      = a : [ Matched a      | a <- shrink a ]
    genericShrink (InDefOf a b)    = b : [ InDefOf a b    | b <- shrink b ]
    genericShrink Here             = []
    genericShrink Unknown          = []

instance CoArbitrary OccursWhere where
  coarbitrary (LeftOfArrow a)  = variant  0 . coarbitrary a
  coarbitrary (DefArg a b c)   = variant  1 . coarbitrary (a, b, c)
  coarbitrary (UnderInf a)     = variant  2 . coarbitrary a
  coarbitrary (VarArg a)       = variant  3 . coarbitrary a
  coarbitrary (MetaArg a)      = variant  4 . coarbitrary a
  coarbitrary (ConArgType a b) = variant  5 . coarbitrary (a, b)
  coarbitrary (IndArgType a b) = variant  6 . coarbitrary (a, b)
  coarbitrary (InClause a b)   = variant  7 . coarbitrary (a, b)
  coarbitrary (Matched a)      = variant  8 . coarbitrary a
  coarbitrary (InDefOf a b)    = variant  9 . coarbitrary (a, b)
  coarbitrary Here             = variant 10
  coarbitrary Unknown          = variant 11

instance Arbitrary Edge where
  arbitrary = Edge <$> arbitrary <*> arbitrary

  shrink (Edge o w) = [ Edge o w | o <- shrink o ] ++
                      [ Edge o w | w <- shrink w ]

instance CoArbitrary Edge where
  coarbitrary (Edge o w) = coarbitrary (o, w)

-- properties moved to Agda.TypeChecking.Positivity.Tests
