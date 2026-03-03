{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
-- {-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}
{-# OPTIONS_GHC -fmax-worker-args=20 #-}
{-# OPTIONS_GHC -fmax-valid-hole-fits=0 -fmax-relevant-binds=3 #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -dno-typeable-binds -ddump-to-file #-}

#if __GLASGOW_HASKELL__ > 902
{-# OPTIONS_GHC -fworker-wrapper-cbv #-}
#endif

module Agda.TypeChecking.Positivity.NewOccurrence where

import Prelude hiding ( null, (!!) )

import Control.Monad.IO.Class

-- import Data.Foldable
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.HashMap.Strict qualified as HMap
import Data.Set (Set)
import Data.Set qualified as Set

import Control.Monad.Primitive
import Data.Hashable
import Data.Bits

import Data.Vector.Mutable qualified as VM
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vector.Primitive qualified as VP
import Data.Vector.Unboxed qualified as VU
import Data.Vector.Unboxed.Mutable qualified as VUM
import Data.Vector.Hashtables qualified as HT

import GHC.Exts
import GHC.Word
import Text.Show

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
-- import Agda.Utils.Map qualified as Map
import Agda.Utils.Maybe
import Agda.Utils.SemiRing
import Agda.Utils.Size
import Agda.Utils.Monad
import Agda.Utils.StrictReader
import Agda.Utils.ExpandCase
import Agda.Utils.Lens
import Agda.Utils.MinimalArray.MutableLifted qualified as Array

#include "MachDeps.h"

{-
NOTE:
- We can't avoid recursing into Unused args becuse we might
  have metavars there, which have constant Mixed arg polarity
  and must be traversed in all cases!
  Proposal: change behavior, skip all Unused subterms
-}


data Path
  = Root
  | LeftOfArrow Path
  | DefArg Path QName Nat         -- ^ in the nth argument of a defined constant
  | MutDefArg Path Int Nat        -- ^ in the nth argument of a def in the current mutual block
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


-- Graph Nodes
--------------------------------------------------------------------------------

newtype Node = Node Word64 deriving Eq

instance Show Node where
  showsPrec p (DefNode x)   =
    showParen (p > 10) (("DefNode " ++) . showsPrec (p + 1) x)
  showsPrec p (ArgNode x y) =
    showParen (p > 10) (("ArgNode " ++) . showsPrec (p + 1) x . (' ':) . showsPrec (p + 1) y)

-- Incantation for getting an Unbox instance for a newtype.
-- Copied from: https://hackage-content.haskell.org/package/vector-0.13.2.0/docs/Data-Vector-Unboxed.html#t:UnboxViaPrim
newtype instance VU.MVector s Node = MV_Word64 (VP.MVector s Word64)
newtype instance VU.Vector    Node = V_Word64  (VP.Vector    Word64)
deriving via (VU.UnboxViaPrim Word64) instance VGM.MVector VU.MVector Node
deriving via (VU.UnboxViaPrim Word64) instance VG.Vector   VU.Vector  Node
instance VU.Unbox Node

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

instance Hashable Node where
  hashWithSalt h (Node n) = fromIntegral (fromIntegral h `combine` fromIntegral n) where
    xor (W# x) (W# y) = W# (xor# x y)
    foldedMul (W# x) (W# y) = case timesWord2# x y of (# hi, lo #) -> W# (xor# hi lo)

    combine :: Word -> Word -> Word
    combine x y = foldedMul (xor x y) factor

    factor :: Word
#if WORD_SIZE_IN_BITS == 64
    factor = 11400714819323198549
#else
    factor = 2654435741
#endif

--------------------------------------------------------------------------------

-- | Top-level arg index that a local variable was bound in, arg polarity of the var itself.
data DefArgInEnv = DefArgInEnv Int [Occurrence]
  deriving Show

data Edge      = Edge Occurrence Path deriving (Eq, Show)
type TargetMap = HT.Dictionary (PrimState IO) VUM.MVector Node VM.MVector Edge
type DefArgs   = HT.Dictionary (PrimState IO) VUM.MVector Int VM.MVector TargetMap
type Mutuals   = HT.Dictionary (PrimState IO) VM.MVector QName VUM.MVector Int

data SourceEntry = SourceEntry QName DefArgs TargetMap
type OccGraph    = Array.IOArray SourceEntry

data OccEnv = OccEnv {
    topDef     :: Int           -- ^ The definition we're working under.
  , topDefArgs :: [DefArgInEnv] -- ^ Occurrence info for definitions args.
  , inf        :: Maybe QName   -- ^ Name for ∞ builtin.
  , locals     :: Int           -- ^ Number of local binders (on the top of the definition args).
  , mutuals    :: Mutuals       -- ^ Definitions in the current mutual group.
  , target     :: Node          -- ^ We add occurrences pointing to this node.
  , path       :: Path          -- ^ Path from the target node to the current position.
  , occ        :: Occurrence    -- ^ Occurence of current position.
  , graph      :: OccGraph
  }

type OccM = ReaderT OccEnv TCM

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
            ~ps <- underAbsReduceM a b \b -> go b
            pure (p:ps)
          _ -> pure []
    liftReduce (go a)

{-# NOINLINE lookupTargetMap #-}
lookupTargetMap :: TargetMap -> Node -> IO (Maybe Edge)
lookupTargetMap = HT.lookup

{-# NOINLINE insertTargetMap #-}
insertTargetMap :: TargetMap -> Node -> Edge -> IO ()
insertTargetMap = HT.insert

{-# NOINLINE lookupDefArgs #-}
lookupDefArgs :: DefArgs -> Int -> IO (Maybe TargetMap)
lookupDefArgs = HT.lookup

{-# NOINLINE insertDefArgs #-}
insertDefArgs :: DefArgs -> Int -> TargetMap -> IO ()
insertDefArgs = HT.insert

{-# NOINLINE addToTargetMap #-}
addToTargetMap :: TargetMap -> Node -> Edge -> IO ()
addToTargetMap tgts tgt e = lookupTargetMap tgts tgt >>= \case
  Nothing -> insertTargetMap tgts tgt e
  Just e' -> insertTargetMap tgts tgt $! mergeEdges e e'

{-# NOINLINE addToDefArgs #-}
addToDefArgs :: DefArgs -> Int -> Node -> Edge -> IO ()
addToDefArgs args i tgt e = lookupDefArgs args i >>= \case
  Just tgts ->
    addToTargetMap tgts tgt e
  Nothing -> do
    tgts <- HT.initialize 1
    insertTargetMap tgts tgt e
    insertDefArgs args i tgts

{-# NOINLINE addDefArgEdgeToGraph #-}
addDefArgEdgeToGraph :: OccGraph -> Int -> Int -> Node -> Edge -> IO ()
addDefArgEdgeToGraph graph src i target e = do
  SourceEntry _ args _ <- Array.read graph src
  addToDefArgs args i target e

{-# NOINLINE addDefEdgeToGraph #-}
addDefEdgeToGraph :: OccGraph -> Int -> Node -> Edge -> IO ()
addDefEdgeToGraph graph src target e = do
  SourceEntry _ _ tgts <- Array.read graph src
  addToTargetMap tgts target e

{-# NOINLINE lookupMutuals #-}
lookupMutuals :: QName -> OccM (Maybe Int)
lookupMutuals q = do
  mutuals <- asks mutuals
  lift $ lift $ HT.lookup mutuals q

{-# NOINLINE lookupMutuals' #-}
lookupMutuals' :: QName -> OccM Int
lookupMutuals' q = do
  mutuals <- asks mutuals
  lift $ lift $ HT.lookup' mutuals q

addDefArgEdge :: Int -> Int -> OccM ()
addDefArgEdge q i = do
  target <- asks target
  path   <- asks path
  occ    <- asks occ
  graph  <- asks graph
  expand \ret -> case occ of
    Unused -> ret $ pure ()
    occ    -> ret $ seq (addDefArgEdgeToGraph graph q i target (Edge occ path)) (pure ())

addDefEdge :: Int -> OccM ()
addDefEdge q = do
  target <- asks target
  path <- asks path
  occ <- asks occ
  graph <- asks graph
  expand \ret -> case occ of
    Unused -> ret $ pure ()
    occ    -> ret $ seq (addDefEdgeToGraph graph q target (Edge occ path)) (pure ())

occurrencesInDefArg :: QName -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArg d p i e = expand \ret -> ret do
  underPathOcc (\p -> DefArg p d i) p $ occurrences e

occurrencesInDefArgArg :: Occurrence -> Int -> Elim -> OccM ()
occurrencesInDefArgArg p i e = expand \ret -> ret do
  underPathOcc (`VarArg` i) p $ occurrences e

occurrencesInMutDefArg :: Int -> Occurrence -> Int -> Elim -> OccM ()
occurrencesInMutDefArg d p i e = expand \ret -> ret $
  local (\e -> e {path = MutDefArg (path e) d i, target = ArgNode d i, occ = p}) $
    occurrences e

lookupDef :: QName -> TCM Definition
lookupDef q = do
  st <- getTC
  let defs  = st ^. stSignature . sigDefinitions
      idefs = st ^. stImports   . sigDefinitions
  case HMap.lookup q defs of
    Just d  -> pure d
    Nothing -> case HMap.lookup q idefs of
      Just d -> pure d
      Nothing -> __IMPOSSIBLE__

class ComputeOccurrences a where
  occurrences :: a -> OccM ()

  {-# INLINE occurrences #-}
  default occurrences :: (Foldable t, ComputeOccurrences b, a ~ t b) => a -> OccM ()
  occurrences = mapM_ occurrences

instance ComputeOccurrences Term where
  occurrences t = expand \ret -> case unSpine t of

    Var x es -> ret do
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
        addDefArgEdge topDef argix
        elims 0 ps es

    Def d es -> ret $ asks inf >>= \case

      -- ∞ application
      Just inf | d == inf -> case es of
        []     -> pure ()
        [_]    -> pure () -- unused arg
        [_, e] -> underPathOcc UnderInf GuardPos $ occurrences e
        _      -> __IMPOSSIBLE__

      _ -> lookupMutuals d >>= \case

        -- it's a mutual definition
        Just di -> do
          addDefEdge di
          expand \ret -> case es of
            [] -> ret $ pure ()  -- we skip the mutualDefOcc in this case
            es -> ret do
              let elims di p i es = expand \ret -> case es of
                    []   -> ret $ pure ()
                    e:es -> ret do occurrencesInMutDefArg di p i e
                                   elims di p (i + 1) es

              defOcc <- liftTCM $ mutualDefOcc d
              elims di defOcc 0 es

        -- not a mutual definition
        Nothing -> do
          def <- liftTCM $ getConstInfo d
          case theDef def of
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

    Con _ _ es -> ret $ occurrences es -- András 2026-02-17: why not push something here?
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

addClauseArgMatches :: NAPs -> OccM ()
addClauseArgMatches ps = underPathSetOcc Matched Mixed $ go 0 ps where
  go :: Int -> NAPs -> OccM ()
  go i ps = expand \ret -> case ps of
    []   -> ret $ pure ()
    p:ps -> ret do
      liftTCM (properlyMatching (namedThing $ unArg p)) >>= \case
        True  -> do topDef <- asks topDef
                    addDefArgEdge topDef i
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

  defOcc <- liftTCM $ mutualDefOcc q
  underPathOcc (`InDefOf` q) defOcc $ expand \ret -> case theDef def of

    Function{funClauses = cs} -> ret do

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
                               addDefArgEdge d i
                               go (i + 1) ps
          go 0 (namedClausePats cl)

    Datatype{dataClause = Just c} -> ret $ occurrences =<< liftTCM (instantiateFull c)

    Datatype{dataPars = np0, dataCons = cs, dataTranspIx = trx} -> ret do
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
        1 -> ret $ addDefArgEdge qi np0
        _ -> ret $ pure ()

      -- add edges for indices
      underPathSetOcc IsIndex Mixed $
        rangeM_ np (size telD - 1) \i -> addDefArgEdge qi i


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

    Record{recClause = Just c} -> ret do
      occurrences =<< liftTCM (instantiateFull c)

    Record{recPars = np, recTel = tel} -> ret do
      let (tel0, tel1) = splitTelescopeAt np tel
      pvars <- liftTCM $ paramsToDefArgs tel0
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

initOccurrences :: [QName] -> IO (OccGraph, Mutuals)
initOccurrences qs = do
  mutuals :: Mutuals <- HT.initialize 1
  forM_ qs \q -> do
    id <- HT.size mutuals
    HT.insert mutuals q id

  s <- HT.size mutuals
  graph <- Array.new s undefined
  let go :: Int -> [QName] -> IO ()
      go i [] =
        pure ()
      go i (q:qs) = do
        tgts <- HT.initialize 1
        args <- HT.initialize 1
        Array.write graph i $! SourceEntry q tgts args
        go (i + 1) qs
  go 0 qs
  pure (graph, mutuals)


buildOccurrenceGraph :: [QName] -> TCM OccGraph
buildOccurrenceGraph qs = do
  inf <- maybe Nothing (\x -> Just $! nameOfInf x) <$> coinductionKit
  (graph, mutuals) <- lift $ initOccurrences qs
  assocs <- lift $ HT.toList mutuals
  forM_ assocs \(q, qi) -> do
    let env = OccEnv qi [] inf 0 mutuals (DefNode qi) Root StrictPos graph
    runReaderT (computeDefOccurrences q qi) env
  pure graph
