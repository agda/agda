{-# LANGUAGE CPP, FlexibleInstances, FlexibleContexts,
             UndecidableInstances #-}

-- | Check that a datatype is strictly positive.
module Agda.TypeChecking.Positivity where

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Monad.Reader

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List as List
import Data.Maybe (mapMaybe)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.TypeChecking.Datatypes (isDataOrRecordType, DataOrRecord(..))
import Agda.TypeChecking.Records (unguardedRecord, recursiveRecord)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (primInf, CoinductionKit(..), coinductionKit)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.SemiRing
import qualified Agda.Utils.Graph as Graph
import Agda.Utils.Graph (Graph)

#include "../undefined.h"

-- | Check that the datatypes in the mutual block containing the given
-- declarations are strictly positive.
checkStrictlyPositive :: Set QName -> TCM ()
checkStrictlyPositive qs = disableDestructiveUpdate $ do
  -- compute the occurrence graph for qs
  reportSDoc "tc.pos.tick" 100 $ text "positivity of" <+> prettyTCM (Set.toList qs)
  g <- Graph.filterEdges (\ (Edge o _) -> o /= Unused) <$> buildOccurrenceGraph qs
  let gstar = Graph.transitiveClosure $ fmap occ g
  reportSDoc "tc.pos.tick" 100 $ text "constructed graph"
  reportSLn "tc.pos.graph" 5 $ "Positivity graph: N=" ++ show (size $ Graph.nodes g) ++
                               " E=" ++ show (length $ Graph.edges g)
  reportSDoc "tc.pos.graph" 10 $ vcat
    [ text "positivity graph for" <+> prettyTCM (Set.toList qs)
    , nest 2 $ prettyTCM g
    ]
  reportSDoc "tc.pos.graph" 50 $ vcat
    [ text "transitive closure of positivity graph for" <+>
      prettyTCM (Set.toList qs)
    , nest 2 $ prettyTCM gstar
    ]

  -- remember argument occurrences for qs in the signature
  mapM_ (setArgs gstar) $ Set.toList qs
  reportSDoc "tc.pos.tick" 100 $ text "set args"

  -- check positivity for all strongly connected components of the graph for qs
  let sccs = Graph.sccs gstar
  reportSDoc "tc.pos.graph.sccs" 15 $ text $ "  sccs = " ++ show sccs
  forM_ sccs $ \ scc -> setMut [ q | DefNode q <- scc ]
  whenM positivityCheckEnabled $
    mapM_ (checkPos g) $ Set.toList qs
  reportSDoc "tc.pos.tick" 100 $ text "checked positivity"

  where
    checkPos g q = do
      -- we check positivity only for data or record definitions
      whenJustM (isDatatype q) $ \ dr -> do
      reportSDoc "tc.pos.check" 10 $ text "Checking positivity of" <+> prettyTCM q
      -- get all pathes from q to q that exhibit a non-strictly occurrence
      -- or, in case of records, any recursive occurrence
      let critical IsData   = \ (Edge o _) -> o <= JustPos
          critical IsRecord = \ (Edge o _) -> o /= Unused
          loops      = filter (critical dr) $ Graph.allPaths (critical dr) (DefNode q) (DefNode q) g

      -- if we have a negative loop, raise error
      forM_ [ how | Edge o how <- loops, o <= JustPos ] $ \ how -> do
          err <- fsep $
            [prettyTCM q] ++ pwords "is not strictly positive, because it occurs" ++
            [prettyTCM how]
          setCurrentRange (getRange q) $ typeError $ GenericError (show err)

      -- if we find an unguarded record, mark it as such
      (\ just noth -> maybe noth just (mhead [ how | Edge o how <- loops, o <= StrictPos ]))
        (\ how -> do
          reportSDoc "tc.pos.record" 5 $ sep
            [ prettyTCM q <+> text "is not guarded, because it occurs"
            , prettyTCM how
            ]
          unguardedRecord q) $
        -- otherwise, if the record is recursive, mark it as well
        forM_ (take 1 [ how | Edge GuardPos how <- loops ]) $ \ how -> do
          reportSDoc "tc.pos.record" 5 $ sep
            [ prettyTCM q <+> text "is recursive, because it occurs"
            , prettyTCM how
            ]
          recursiveRecord q

    occ (Edge o _) = o

    isDatatype q = do
      def <- theDef <$> getConstInfo q
      return $ case def of
        Datatype{dataClause = Nothing} -> Just IsData
        Record  {recClause  = Nothing} -> Just IsRecord
        _ -> Nothing

    -- Set the mutually recursive identifiers for a SCC.
    setMut []  = return ()  -- nothing to do
    setMut [q] = return ()  -- no mutual recursion
    setMut qs  = forM_ qs $ \ q -> setMutual q (delete q qs)

    -- Set the polarity of the arguments to a definition
    setArgs g q = do
      reportSDoc "tc.pos.args" 5 $ text "checking args of" <+> prettyTCM q
      n <- getDefArity =<< getConstInfo q
      let nArgs = maximum $ n :
                    [ i + 1 | (ArgNode q1 i) <- Set.toList $ Graph.nodes g
                    , q1 == q ]
          findOcc i = maybe Unused id $ Graph.lookup (ArgNode q i) (DefNode q) g
          args = map findOcc [0..nArgs - 1]
      reportSDoc "tc.pos.args" 10 $ sep
        [ text "args of" <+> prettyTCM q <+> text "="
        , nest 2 $ prettyList $ map (text . show) args
        ]
      -- The list args can take a long time to compute, but contains
      -- small elements, and is stored in the interface (right?), so
      -- it is computed deep-strictly.
      setArgOccurrences q $!! args

getDefArity def = case theDef def of
  Function{ funClauses = cs, funProjection = proj } -> do
    let dropped = maybe 0 (subtract 1 . snd) proj
    subtract dropped . arity <$> instantiateFull (defType def)
  Datatype{ dataPars = n } -> return n
  Record{ recPars = n }    -> return n
  _                        -> return 0

-- Specification of occurrences -------------------------------------------

-- | 'Occurrence' is a complete lattice with least element 'Mixed'
--   and greatest element 'Unused'.
--
--   It forms a commutative semiring where 'oplus' is meet (glb)
--   and 'otimes' is composition. Both operations are idempotent.
--
--   For 'oplus', 'Unused' is neutral (zero) and 'Mixed' is dominant.
--   For 'otimes', 'StrictPos' is neutral (one) and 'Unused' is dominant.

instance SemiRing Occurrence where
  oplus Mixed _           = Mixed     -- dominant
  oplus _ Mixed           = Mixed
  oplus Unused o          = o         -- neutral
  oplus o Unused          = o
  oplus JustNeg  JustNeg  = JustNeg
  oplus JustNeg  o        = Mixed     -- negative and any form of positve
  oplus o        JustNeg  = Mixed
  oplus GuardPos o        = o         -- second-rank neutral
  oplus o GuardPos        = o
  oplus StrictPos o       = o         -- third-rank neutral
  oplus o StrictPos       = o
  oplus JustPos JustPos   = JustPos

  otimes Unused _            = Unused     -- dominant
  otimes _ Unused            = Unused
  otimes Mixed _             = Mixed      -- second-rank dominance
  otimes _ Mixed             = Mixed
  otimes JustNeg JustNeg     = JustPos
  otimes JustNeg _           = JustNeg    -- third-rank dominance
  otimes _ JustNeg           = JustNeg
  otimes JustPos _           = JustPos    -- fourth-rank dominance
  otimes _ JustPos           = JustPos
  otimes GuardPos _          = GuardPos   -- _ `elem` [StrictPos, GuardPos]
  otimes _ GuardPos          = GuardPos
  otimes StrictPos StrictPos = StrictPos  -- neutral

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
  deriving (Show, Eq)

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

      uniq (x:y:xs)
        | x == y  = uniq (x:xs)
      uniq (x:xs) = x : uniq xs
      uniq []     = []

      prettyOs [] = __IMPOSSIBLE__
      prettyOs [o] = prettyO o <> text "."
      prettyOs (o:os) = prettyO o <> text ", which occurs" <+> prettyOs os

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
getOccurrences :: ComputeOccurrences a => [Maybe Item] -> a -> TCM Occurrences
getOccurrences vars a = do
  kit <- coinductionKit
  return $ runReader (occurrences a) $ OccEnv vars $ fmap nameOfInf kit

class ComputeOccurrences a where
  occurrences :: a -> OccM Occurrences

instance ComputeOccurrences Clause where
  occurrences (Clause{ clausePats = ps0, clauseBody = body }) = do
    let ps = map unArg ps0
    (concatOccurs (mapMaybe matching (zip [0..] ps)) >+<) <$>
      walk (patItems ps) body
    where
      matching (i, p)
        | properlyMatching p = Just $ occursAs Matched $ here $ AnArg i
        | otherwise          = Nothing
{-
      matching (i, VarP{}) = Nothing
      matching (i, DotP{}) = Nothing
      matching (i, ConP _ Just{} _) = Nothing -- record patterns are not matches
      matching (i, _     ) = Just (occursAs Matched $ here (AnArg i))
-}

      walk _         NoBody     = return $ Map.empty
      walk []        (Body v)   = occurrences v
      walk (i : pis) (Bind b)   = withExtendedOccEnv i $ walk pis $ absBody b
      walk []        Bind{}     = __IMPOSSIBLE__
      walk (_ : _)   Body{}     = __IMPOSSIBLE__

      -- @patItems ps@ creates a map from the pattern variables of @ps@
      -- to the index of the argument they are bound in.
      -- This map is given as a list.
      patItems ps = concat $ zipWith patItem [0..] ps

      -- @patItem i p@ replicates index @i@ as often as there are
      -- pattern variables in @p@
      patItem i p = replicate (nVars p) (Just (AnArg i))

      -- @nVars p@ computes the number of variables bound by pattern @p@
      nVars p = case p of
        VarP{}      -> 1
        DotP{}      -> 1
        ConP _ _ ps -> sum $ map (nVars . unArg) ps
        LitP{}      -> 0

instance ComputeOccurrences Term where
  occurrences v = case v of
    Var i args -> do
      vars <- asks vars
      occs <- occurrences args
      return $ maybe Map.empty here (index vars i)
               >+< occursAs VarArg occs
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
    Lit{}        -> return $ Map.empty
    Sort{}       -> return $ Map.empty
    DontCare _   -> return $ Map.empty -- Andreas, 2011-09-09: do we need to check for negative occurrences in irrelevant positions?
    Shared p     -> occurrences $ derefPtr p
    where
      -- Apparently some development version of GHC chokes if the
      -- following line is replaced by vs ! i.
      index vs i
        | i < length vs = vs !! i
        | otherwise     = __IMPOSSIBLE__

instance ComputeOccurrences Level where
  occurrences (Max as) = occurrences as

instance ComputeOccurrences PlusLevel where
  occurrences ClosedLevel{} = return $ Map.empty
  occurrences (Plus _ l)    = occurrences l

instance ComputeOccurrences LevelAtom where
  occurrences l = case l of
    MetaLevel _ vs   -> occursAs MetaArg <$> occurrences vs
    BlockedLevel _ v -> occurrences v
    NeutralLevel v   -> occurrences v
    UnreducedLevel v -> occurrences v

instance ComputeOccurrences Type where
  occurrences (El _ v) = occurrences v

instance ComputeOccurrences a => ComputeOccurrences (Tele a) where
  occurrences EmptyTel        = return $ Map.empty
  occurrences (ExtendTel a b) = occurrences (a, b)

instance ComputeOccurrences a => ComputeOccurrences (Abs a) where
  occurrences (Abs   _ b) = withExtendedOccEnv Nothing $ occurrences b
  occurrences (NoAbs _ b) = occurrences b

instance ComputeOccurrences a => ComputeOccurrences (I.Arg a) where
  occurrences = occurrences . unArg

instance ComputeOccurrences a => ComputeOccurrences (I.Dom a) where
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
computeOccurrences q = do
  def <- getConstInfo q
  occursAs (InDefOf q) <$> case theDef def of
    Function{funClauses = cs} -> do
      n  <- getDefArity def
      cs <- map (etaExpandClause n) <$> instantiateFull cs
      concatOccurs . zipWith (occursAs . InClause) [0..] <$>
        mapM (getOccurrences []) cs
    Datatype{dataClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Datatype{dataPars = np, dataCons = cs}       -> do
      let conOcc c = do
            a <- defType <$> getConstInfo c
            TelV tel t <- telView' <$> normalise a
            let indices = case unEl t of
                            Def _ vs -> genericDrop np vs
                            _        -> __IMPOSSIBLE__
            let tel'    = telFromList $ genericDrop np $ telToList tel
                vars np = map (Just . AnArg) $ downFrom np
            (>+<) <$> (occursAs (ConArgType c) <$> getOccurrences (vars np) tel')
                  <*> (occursAs (IndArgType c) . onlyVarsUpTo np <$> getOccurrences (vars $ size tel) indices)
      concatOccurs <$> mapM conOcc cs
    Record{recClause = Just c} -> getOccurrences [] =<< instantiateFull c
    Record{recPars = np, recTel = tel} -> do
      let tel' = telFromList $ genericDrop np $ telToList tel
          vars = map (Just . AnArg) $ downFrom np
      getOccurrences vars =<< instantiateFull tel'

    -- Arguments to other kinds of definitions are hard-wired.
    Constructor{} -> return Map.empty
    Axiom{}       -> return Map.empty
    Primitive{}   -> return Map.empty

-- | Eta expand a clause to have the given number of variables.
--   Warning: doesn't update telescope or permutation!
--   This is used instead of special treatment of lambdas
--   (which was unsound: issue 121)
etaExpandClause :: Nat -> Clause -> Clause
etaExpandClause n c@Clause{ clausePats = ps, clauseBody = b }
  | m <= 0    = c
  | otherwise = c { clausePats = ps ++ genericReplicate m (defaultArg $ VarP "_")
                  , clauseBody = liftBody m b
                  }
  where
    m = n - genericLength ps

    bind 0 = id
    bind n = Bind . Abs "_" . bind (n - 1)

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

instance PrettyTCM Occurrence where
  prettyTCM GuardPos  = text "-[g+]->"
  prettyTCM StrictPos = text "-[++]->"
  prettyTCM JustPos   = text "-[+]->"
  prettyTCM JustNeg   = text "-[-]->"
  prettyTCM Mixed     = text "-[*]->"
  prettyTCM Unused    = text "-[ ]->"

instance PrettyTCM n => PrettyTCM (n, Edge) where
  prettyTCM (n, Edge o w) =
    prettyTCM o <+> prettyTCM n <+> fsep (pwords $ show w)

instance PrettyTCM n => PrettyTCM (n, Occurrence) where
  prettyTCM (n, o) = prettyTCM o <+> prettyTCM n

instance (PrettyTCM n, PrettyTCM (n, e)) => PrettyTCM (Graph n e) where
  prettyTCM g = vcat $ map pr $ Map.assocs $ Graph.unGraph g
    where
      pr (n, es) = sep
        [ prettyTCM n
        , nest 2 $ vcat $ map prettyTCM $ Map.assocs es
        ]

data Edge = Edge Occurrence OccursWhere
  deriving (Show)

-- | These operations form a semiring if we quotient by the relation
-- \"the 'Occurrence' components are equal\".

instance SemiRing Edge where
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

buildOccurrenceGraph :: Set QName -> TCM (Graph Node Edge)
buildOccurrenceGraph qs = Graph.unions <$> mapM defGraph (Set.toList qs)
  where
    defGraph :: QName -> TCM (Graph Node Edge)
    defGraph q = do
      occs <- computeOccurrences q
      let onItem (item, occs) = do
            es <- mapM (computeEdge qs) occs
            return $ Graph.unions $
                map (\(b, w) -> Graph.singleton (itemToNode item) b w) es
      Graph.unions <$> mapM onItem (Map.assocs occs)
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
