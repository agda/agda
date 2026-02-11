{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

{- | Various utility functions dealing with the non-linear, higher-order
     patterns used for rewrite rules.
-}

module Agda.TypeChecking.Rewriting.NonLinPattern where

import Prelude hiding ( null )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Defs
import Agda.Syntax.Internal.MetaVars ( AllMetas, unblockOnAllMetasIn )

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Irrelevance ( isDefSing, isPatternVar )
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Primitive.Cubical.Base

import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size
import qualified Agda.Utils.VarSet as VarSet
import Agda.Utils.VarSet (VarSet)
import Data.Foldable (Foldable(fold))

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.
--   The first two arguments indicate whether the pattern we are under is
--   definitionally singular. Specifically, the first tracks the definitional
--   singularity of the last |PDef|/|PBoundVar| match, while the second tracks
--   the current definitional singularity.
--   The third argument and fourth arguments, k0 and k1, partition the context
--   into three chunks: the local context, the telescope of
--   of pattern variables associated with the rewrite and the pattern-lambda
--   bound variables.
--   The fifth argument is the type of the term.

class PatternFrom a b where
  patternFrom :: DefSing -> DefSing -> Int -> Int -> TypeOf a -> a -> TCM b

instance (PatternFrom a b) => PatternFrom (Arg a) (Arg b) where
  patternFrom r0 r1 k0 k1 t u
    = let r1' = r1 `maxDefSing` relToDefSing (getRelevance u)
      in  traverse (patternFrom r0 r1' k0 k1 $ unDom t) u

instance PatternFrom Elims PElims where
  patternFrom r0 r1 k0 k1 (t,hd) = \case
    [] -> return []
    (Apply u : es) -> do
      (a, b) <- assertPi t
      p   <- patternFrom r0 r1 k0 k1 a u
      let t'  = absApp b (unArg u)
      let hd' = hd . (Apply u:)
      ps  <- patternFrom r0 r1 k0 k1 (t',hd') es
      return $ Apply p : ps
    (IApply x y i : es) -> do
      (s, q, l, b, u, v) <- assertPath t
      let t' = El s $ unArg b `apply` [ defaultArg i ]
      let hd' = hd . (IApply x y i:)
      interval <- primIntervalType
      p   <- patternFrom r0 r1 k0 k1 interval i
      ps  <- patternFrom r0 r1 k0 k1 (t',hd') es
      return $ IApply (PTerm x) (PTerm y) p : ps
    (Proj o f : es) -> do
      (a,b) <- assertProjOf f t
      let u = hd []
          t' = b `absApp` u
      hd' <- applyDef o f (argFromDom a $> u)
      ps  <- patternFrom r0 r1 k0 k1 (t',applyE hd') es
      return $ Proj o f : ps

instance (PatternFrom a b) => PatternFrom (Dom a) (Dom b) where
  patternFrom r0 r1 k0 k1 t = traverse $ patternFrom r0 r1 k0 k1 t

instance PatternFrom Type NLPType where
  patternFrom r0 r1 k0 k1 _ a = workOnTypes $
    NLPType <$> patternFrom r0 r1 k0 k1 () (getSort a)
            <*> patternFrom r0 r1 k0 k1 (sort $ getSort a) (unEl a)

instance PatternFrom Sort NLPSort where
  patternFrom r0 r1 k0 k1 _ s = do
    s <- abortIfBlocked s
    case s of
      Univ u l -> PUniv u <$> patternFrom r0 r1 k0 k1 () l
      Inf u n  -> return $ PInf u n
      SizeUniv -> return PSizeUniv
      LockUniv -> return PLockUniv
      LevelUniv -> return PLevelUniv
      IntervalUniv -> return PIntervalUniv
      PiSort _ _ _ -> __IMPOSSIBLE__
      FunSort _ _ -> __IMPOSSIBLE__
      UnivSort _ -> __IMPOSSIBLE__
      MetaS{}  -> __IMPOSSIBLE__
      DefS{}   -> __IMPOSSIBLE__
      DummyS s -> do
        reportS "impossible" 10
          [ "patternFrom: hit dummy sort with content:"
          , s
          ]
        __IMPOSSIBLE__

instance PatternFrom Level NLPat where
  patternFrom r0 r1 k0 k1 _ l = do
    t <- levelType
    v <- reallyUnLevelView l
    patternFrom r0 r1 k0 k1 t v

instance PatternFrom Term NLPat where
  patternFrom r0 r1 k0 k1 t v = do
    t <- abortIfBlocked t
    etaRecord <- isEtaRecordType t
    r1 <- maxDefSing r1 <$> isDefSing k0 k1 t
    v <- unLevel =<< abortIfBlocked v
    reportSDoc "rewriting.build" 60 $ sep
      [ "building a pattern from term v = " <+> prettyTCM v
      , " of type " <+> prettyTCM t
      ]
    pview <- pathViewAsPi'whnf
    let done = blockOnMetasIn v >> return (PTerm v)
    case (unEl t , stripDontCare v) of
      (Pi a b , _) -> do
        let body = raise 1 v `apply` [ Arg (domInfo a) $ var 0 ]
        p <- addContext a (patternFrom r0 r1 (k0 + 1) (k1 + 1) (absBody b) body)
        return $ PLam (domInfo a) $ Abs (absName b) p
      _ | Left ((a,b),(x,y)) <- pview t -> do
        let body = raise 1 v `applyE` [ IApply (raise 1 $ x) (raise 1 $ y) $ var 0 ]
        p <- addContext a (patternFrom r0 r1 (k0 + 1) (k1 + 1) (absBody b) body)
        return $ PLam (domInfo a) $ Abs (absName b) p
      (_ , Var i es)
       -- Variables before k0 are locally bound outside the rewrite telescope
       -- Variables after k1 are bound in higher order patterns
       | not $ isPatternVar k0 k1 i -> do
           t <- typeOfBV i
           PBoundVar i <$> patternFrom r1 r1 k0 k1 (t , Var i) es
       -- The arguments of `var i` should be distinct bound variables
       -- in order to build a Miller pattern
       | Just vs <- allApplyElims es -> do
           TelV tel rest <- telViewPath =<< typeOfBV i
           unless (natSize tel >= natSize vs) $ blockOnMetasIn rest >> addContext tel (errNotPi rest)
           let ts = applySubst (parallelS $ reverse $ map unArg vs) $ map unDom $ flattenTel tel
           mbvs <- forM (zip ts vs) $ \(t , v) -> do
             blockOnMetasIn (v,t)
             isEtaVar (unArg v) t >>= \case
               Just j | k0 < j || j < k1 -> return $ Just $ v $> j
               _                         -> return Nothing
           case sequence mbvs of
             Just bvs | fastDistinct bvs -> do
               let allBoundVars = VarSet.full k1
                   ok = not (isAlwaysSing r1) ||
                        VarSet.fromList (map unArg bvs) == allBoundVars
               if ok then return (PVar r0 i bvs) else done
                 -- Important: Definitional singularity at |PVar|s should be
                 -- that of the surrounding pattern (|r| rather than |r'|).
                 -- If only the variable itself might be definitionally singular
                 -- that is not a problem.
             _ -> done
       | otherwise -> done
      (_ , _ ) | Just (d, pars) <- etaRecord -> do
        RecordDefn def <- theDef <$> getConstInfo d
        (tel, c, ci, vs) <- etaExpandRecord_ d pars def v
        ct <- assertConOf c t
        PDef (conName c) <$> patternFrom r1 r1 k0 k1 (ct , Con c ci) (map Apply vs)
      (_ , Lam{})   -> errNotPi t
      (_ , Lit{})   -> done
      (_ , Def f es) | isAlwaysSing r1 -> done
      (_ , Def f es) -> do
        Def lsuc [] <- primLevelSuc
        Def lmax [] <- primLevelMax
        case es of
          [x]     | f == lsuc -> done
          [x , y] | f == lmax -> done
          _                   -> do
            ft <- defType <$> getConstInfo f
            PDef f <$> patternFrom r1 r1 k0 k1 (ft , Def f) es
      (_ , Con c ci vs) | isAlwaysSing r1 -> done
      (_ , Con c ci vs) -> do
        ct <- assertConOf c t
        PDef (conName c) <$> patternFrom r1 r1 k0 k1 (ct , Con c ci) vs
      (_ , Pi a b) | isAlwaysSing r1 -> done
      (_ , Pi a b) -> do
        pa <- patternFrom r0 r1 k0 k1 () a
        pb <- addContext a (patternFrom r0 r1 (k0 + 1) (k1 + 1) () $ absBody b)
        return $ PPi pa (Abs (absName b) pb)
      (_ , Sort s)     -> PSort <$> patternFrom r0 r1 k0 k1 () s
      (_ , Level l)    -> __IMPOSSIBLE__
      (_ , DontCare{}) -> __IMPOSSIBLE__
      (_ , MetaV m _)  -> __IMPOSSIBLE__
      (_ , Dummy s _)  -> __IMPOSSIBLE_VERBOSE__ (show s)

-- | Convert from a non-linear pattern to a term.

class NLPatToTerm p a where
  nlPatToTerm :: PureTCM m => p -> m a

  default nlPatToTerm ::
    ( NLPatToTerm p' a', Traversable f, p ~ f p', a ~ f a'
    , PureTCM m
    ) => p -> m a
  nlPatToTerm = traverse nlPatToTerm

instance NLPatToTerm p a => NLPatToTerm [p] [a] where
instance NLPatToTerm p a => NLPatToTerm (Arg p) (Arg a) where
instance NLPatToTerm p a => NLPatToTerm (Dom p) (Dom a) where
instance NLPatToTerm p a => NLPatToTerm (Elim' p) (Elim' a) where
instance NLPatToTerm p a => NLPatToTerm (Abs p) (Abs a) where

instance NLPatToTerm Nat Term where
  nlPatToTerm = return . var

instance NLPatToTerm NLPat Term where
  nlPatToTerm = \case
    PVar s i xs    -> Var i . map Apply <$> nlPatToTerm xs
    PTerm u        -> return u
    PDef f es      -> (theDef <$> getConstInfo f) >>= \case
      Constructor{ conSrcCon = c } -> Con c ConOSystem <$> nlPatToTerm es
      _                            -> Def f <$> nlPatToTerm es
    PLam i u       -> Lam i <$> nlPatToTerm u
    PPi a b        -> Pi    <$> nlPatToTerm a <*> nlPatToTerm b
    PSort s        -> Sort  <$> nlPatToTerm s
    PBoundVar i es -> Var i <$> nlPatToTerm es

instance NLPatToTerm NLPat Level where
  nlPatToTerm = nlPatToTerm >=> levelView

instance NLPatToTerm NLPType Type where
  nlPatToTerm (NLPType s a) = El <$> nlPatToTerm s <*> nlPatToTerm a

instance NLPatToTerm NLPSort Sort where
  nlPatToTerm (PUniv u l) = Univ u <$> nlPatToTerm l
  nlPatToTerm (PInf u n) = return $ Inf u n
  nlPatToTerm PSizeUniv = return SizeUniv
  nlPatToTerm PLockUniv = return LockUniv
  nlPatToTerm PLevelUniv = return LevelUniv
  nlPatToTerm PIntervalUniv = return IntervalUniv

data PatVars = PatVars
  { neverSingPatVars :: VarSet
      -- ^ Variables bound in never definitionally singular contexts
  , maybeSingPatVars :: VarSet
      -- ^ Variables bound in possibly definitionally singular contexts
  }
  deriving (Eq)

instance Null PatVars where
  empty = PatVars empty empty
  null (PatVars ps ps') = null ps && null ps'

instance Semigroup PatVars where
  PatVars ps ps' <> PatVars qs qs' = PatVars (ps <> qs) (ps' <> qs')

instance Monoid PatVars where
  mempty = PatVars mempty mempty

instance Singleton (DefSing, Int) PatVars where
  singleton (NeverSing,  x) = PatVars (singleton x) empty
  singleton (MaybeSing,  x) = PatVars empty (singleton x)
  singleton (AlwaysSing, x) = __IMPOSSIBLE__

-- | Gather the set of pattern variables of a non-linear pattern
class NLPatVars a where
  nlPatVarsUnder :: Int -> a -> PatVars

  default nlPatVarsUnder ::
    ( NLPatVars p, Foldable f, Functor f, a ~ f p
    ) => Int -> a -> PatVars
  nlPatVarsUnder k x = fold $ nlPatVarsUnder k <$> x

  nlPatVars :: a -> PatVars
  nlPatVars = nlPatVarsUnder 0

instance NLPatVars NLPType where
  nlPatVarsUnder k (NLPType l a) = nlPatVarsUnder k (l, a)

instance NLPatVars NLPSort where
  nlPatVarsUnder k = \case
    PUniv _ l   -> nlPatVarsUnder k l
    PInf f n  -> empty
    PSizeUniv -> empty
    PLockUniv -> empty
    PLevelUniv -> empty
    PIntervalUniv -> empty

instance NLPatVars NLPat where
  nlPatVarsUnder k = \case
      PVar s i _     -> singleton (s, i - k)
      PDef _ es      -> nlPatVarsUnder k es
      PLam _ p       -> nlPatVarsUnder k p
      PPi a b        -> nlPatVarsUnder k (a, b)
      PSort s        -> nlPatVarsUnder k s
      PBoundVar _ es -> nlPatVarsUnder k es
      PTerm{}        -> empty

instance (NLPatVars a, NLPatVars b) => NLPatVars (a,b) where
  nlPatVarsUnder k (a,b) = nlPatVarsUnder k a <> nlPatVarsUnder k b

instance NLPatVars a => NLPatVars (Abs a) where
  nlPatVarsUnder k = \case
    Abs   _ v -> nlPatVarsUnder (k + 1) v
    NoAbs _ v -> nlPatVarsUnder k v

instance NLPatVars a => NLPatVars (Arg a) where
instance NLPatVars a => NLPatVars (Dom a) where
instance NLPatVars a => NLPatVars (Elim' a) where
instance NLPatVars PElims where

-- | Get all symbols that a non-linear pattern matches against
class GetMatchables a where
  getMatchables :: a -> [QName]

  default getMatchables :: (Foldable f, GetMatchables a', a ~ f a') => a -> [QName]
  getMatchables = foldMap getMatchables

instance GetMatchables a => GetMatchables [a] where
instance GetMatchables a => GetMatchables (Arg a) where
instance GetMatchables a => GetMatchables (Dom a) where
instance GetMatchables a => GetMatchables (Elim' a) where
instance GetMatchables a => GetMatchables (Abs a) where

instance (GetMatchables a, GetMatchables b) => GetMatchables (a,b) where
  getMatchables (x,y) = getMatchables x ++ getMatchables y

instance GetMatchables NLPat where
  getMatchables p =
    case p of
      PVar{}         -> empty
      PDef f es      -> singleton f ++ getMatchables es
      PLam _ x       -> getMatchables x
      PPi a b        -> getMatchables (a,b)
      PSort s        -> getMatchables s
      PBoundVar i es -> getMatchables es
      PTerm u        -> getMatchables u

instance GetMatchables NLPType where
  getMatchables = getMatchables . nlpTypeUnEl

instance GetMatchables NLPSort where
  getMatchables = \case
    PUniv _ l -> getMatchables l
    PInf f n  -> empty
    PSizeUniv -> empty
    PLockUniv -> empty
    PLevelUniv -> empty
    PIntervalUniv -> empty

instance GetMatchables Term where
  getMatchables = getDefs' __IMPOSSIBLE__ singleton

instance GetMatchables RewriteRule where
  getMatchables = getMatchables . rewPats

-- Throws a pattern violation if the given term contains any
-- metavariables.
blockOnMetasIn :: (MonadBlock m, AllMetas t) => t -> m ()
blockOnMetasIn t = case unblockOnAllMetasIn t of
  UnblockOnAll ms | null ms -> return ()
  b -> patternViolation b

-- Helper functions


assertPi :: Type -> TCM (Dom Type, Abs Type)
assertPi t = abortIfBlocked t >>= \case
  El _ (Pi a b) -> return (a,b)
  t             -> errNotPi t

errNotPi :: Type -> TCM a
errNotPi t = typeError . IlltypedRewriteRule =<< fsep
    [ prettyTCM t
    , "should be a function type, but it isn't."
    , "Do you have any non-confluent rewrite rules?"
    ]

assertPath :: Type -> TCM (Sort, QName, Arg Term, Arg Term, Arg Term, Arg Term)
assertPath t = abortIfBlocked t >>= pathView >>= \case
  PathType s q l b u v -> return (s,q,l,b,u,v)
  OType t -> errNotPath t

errNotPath :: Type -> TCM a
errNotPath t = typeError . IlltypedRewriteRule =<< fsep
    [ prettyTCM t
    , "should be a path type, but it isn't."
    , "Do you have any non-confluent rewrite rules?"
    ]

assertProjOf :: QName -> Type -> TCM (Dom Type, Abs Type)
assertProjOf f t = do
  t <- abortIfBlocked t
  getDefType f t >>= \case
    Just (El _ (Pi a b)) -> return (a,b)
    _ -> errNotProjOf f t

errNotProjOf :: QName -> Type -> TCM a
errNotProjOf f t = typeError . IlltypedRewriteRule =<< fsep
      [ prettyTCM f , "should be a projection from type"
      , prettyTCM t , "but it isn't."
      , "Do you have any non-confluent rewrite rules?"
      ]

assertConOf :: ConHead -> Type -> TCM Type
assertConOf c t = getFullyAppliedConType c t >>= \case
    Just (_ , ct) -> return ct
    Nothing -> errNotConOf c t

errNotConOf :: ConHead -> Type -> TCM a
errNotConOf c t = typeError . IlltypedRewriteRule =<< fsep
      [ prettyTCM c , "should be a constructor of type"
      , prettyTCM t , "but it isn't."
      , "Do you have any non-confluent rewrite rules?"
      ]
