{-# LANGUAGE CPP               #-}

-- Initially authored by Andreas, 2013-10-22.

-- | A bidirectional type checker for internal syntax.
--
--   Performs checking on unreduced terms.
--   With the exception that projection-like function applications
--   have to be reduced since they break bidirectionality.

module Agda.TypeChecking.CheckInternal
  ( checkType
  , checkType'
  , checkSort
  , checkInternal
  , checkInternal'
  , Action(..), defaultAction, eraseUnusedAction
  , infer
  , inferSort
  , shouldBeSort
  ) where

import Control.Arrow ((&&&), (***), first, second)
import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes -- (getConType, getFullyAppliedConType)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.ProjectionLike (elimView)
import Agda.TypeChecking.Records (getDefType)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Telescope


import Agda.Utils.Functor (($>))
import Agda.Utils.Monad
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- * Bidirectional rechecker

-- -- | Entry point for e.g. checking WithFunctionType.
-- checkType :: Type -> TCM ()
-- checkType t = -- dontAssignMetas $ ignoreSorts $
--   checkInternal (unEl t) (sort Inf)

-- | Entry point for e.g. checking WithFunctionType.
checkType :: Type -> TCM ()
checkType t = void $ checkType' t

-- | Check a type and infer its sort.
--
--   Necessary because of PTS rule @(SizeUniv, Set i, Set i)@
--   but @SizeUniv@ is not included in any @Set i@.
--
--   This algorithm follows
--     Abel, Coquand, Dybjer, MPC 08,
--     Verifying a Semantic βη-Conversion Test for Martin-Löf Type Theory
--
checkType' :: Type -> TCM Sort
checkType' t = do
  reportSDoc "tc.check.internal" 20 $ sep
    [ "checking internal type "
    , prettyTCM t
    ]
  v <- elimView True $ unEl t -- bring projection-like funs in post-fix form
  case v of
    Pi a b -> do
      s1 <- checkType' $ unDom a
      s2 <- (b $>) <$> do
        let goInside = case b of Abs{}   -> addContext (absName b, a)
                                 NoAbs{} -> id
        goInside $ checkType' $ unAbs b
      inferPiSort s1 s2
    Sort s -> do
      _ <- checkSort defaultAction s
      inferUnivSort s
    Var i es   -> do
      a <- typeOfBV i
      checkTypeSpine a (Var i   []) es
    Def f es   -> do  -- not a projection-like fun
      a <- defType <$> getConstInfo f
      checkTypeSpine a (Def f   []) es
    MetaV x es -> do -- we assume meta instantiations to be well-typed
      a <- metaType x
      checkTypeSpine a (MetaV x []) es
    v@Lam{}    -> typeError $ InvalidType v
    v@Con{}    -> typeError $ InvalidType v
    v@Lit{}    -> typeError $ InvalidType v
    v@Level{}  -> typeError $ InvalidType v
    DontCare v -> checkType' $ t $> v
    Dummy s    -> __IMPOSSIBLE_VERBOSE__ s

checkTypeSpine :: Type -> Term -> Elims -> TCM Sort
checkTypeSpine a self es = shouldBeSort =<< do snd <$> inferSpine a self es


-- | 'checkInternal' traverses the whole 'Term', and we can use this
--   traversal to modify the term.
data Action = Action
  { preAction  :: Type -> Term -> TCM Term
    -- ^ Called on each subterm before the checker runs.
  , postAction :: Type -> Term -> TCM Term
    -- ^ Called on each subterm after the type checking.
  , relevanceAction :: Relevance -> Relevance -> Relevance
    -- ^ Called for each @ArgInfo@.
    --   The first 'Relevance' is from the type,
    --   the second from the term.
  }

-- | The default action is to not change the 'Term' at all.
defaultAction :: Action
defaultAction = Action
  { preAction       = \ _ -> return
  , postAction      = \ _ -> return
  , relevanceAction = \ _ -> id
  }

eraseUnusedAction :: Action
eraseUnusedAction = defaultAction { postAction = eraseUnused }
  where
    eraseUnused :: Type -> Term -> TCM Term
    eraseUnused t v = case v of
      Def f es -> do
        pols <- getPolarity f
        return $ Def f $ eraseIfNonvariant pols es
      _        -> return v

    eraseIfNonvariant :: [Polarity] -> Elims -> Elims
    eraseIfNonvariant []                  es             = es
    eraseIfNonvariant pols                []             = []
    eraseIfNonvariant (Nonvariant : pols) (e : es) = (fmap DontCare e) : eraseIfNonvariant pols es
    eraseIfNonvariant (_          : pols) (e : es) = e : eraseIfNonvariant pols es

-- | Entry point for term checking.
checkInternal :: Term -> Type -> TCM ()
checkInternal v t = void $ checkInternal' defaultAction v t

checkInternal' :: Action -> Term -> Type -> TCM Term
checkInternal' action v t = do
  reportSDoc "tc.check.internal" 20 $ sep
    [ "checking internal "
    , nest 2 $ sep [ prettyTCM v <+> ":"
                   , nest 2 $ prettyTCM t ] ]
  -- Bring projection-like funs in post-fix form,
  -- even lone ones (True).
  v <- elimView True =<< preAction action t v
  postAction action t =<< case v of
    Var i es   -> do
      a <- typeOfBV i
      checkSpine action a (Var i []) es t
    Def f es   -> do  -- f is not projection(-like)!
      a <- defType <$> getConstInfo f
      checkSpine action a (Def f []) es t
    MetaV x es -> do -- we assume meta instantiations to be well-typed
      a <- metaType x
      checkSpine action a (MetaV x []) es t
    Con c ci vs -> do
      -- We need to fully apply the constructor to make getConType work!
      fullyApplyCon c vs t $ \ _d _dt _pars a vs' tel t -> do
        Con c ci vs2 <- checkSpine action a (Con c ci []) vs' t
        -- Strip away the extra arguments
        return $ applySubst (strengthenS __IMPOSSIBLE__ (size tel))
          $ Con c ci $ take (length vs) vs2
    Lit l      -> Lit l <$ ((`subtype` t) =<< litType l)
    Lam ai vb  -> do
      (a, b) <- maybe (shouldBePi t) return =<< isPath t
      ai <- checkArgInfo action ai $ domInfo a
      addContext (suggest vb b, a) $ do
        Lam ai . Abs (absName vb) <$> checkInternal' action (absBody vb) (absBody b)
    Pi a b     -> do
      s <- shouldBeSort t
      when (s == SizeUniv) $ typeError $ FunctionTypeInSizeUniv v
      let st  = sort s
          sa  = getSort a
          sb  = getSort (unAbs b)
          mkDom v = El sa v <$ a
          mkRng v = fmap (v <$) b
          -- Preserve NoAbs
          goInside = case b of Abs{}   -> addContext (absName b, a)
                               NoAbs{} -> id
      a <- mkDom <$> checkInternal' action (unEl $ unDom a) (sort sa)
      -- TODO: checkPTS sa sb s
      goInside $ Pi a . mkRng <$> checkInternal' action (unEl $ unAbs b) (sort sb)
    Sort s     -> do
      s <- checkSort action s
      Sort s <$ ((sortFitsIn s) =<< shouldBeSort t) -- sortFitsIn ensures @s /= Inf@
    Level l    -> do
      l <- checkLevel action l
      Level l <$ ((`subtype` t) =<< levelType)
    DontCare v -> DontCare <$> checkInternal' action v t
    Dummy s -> __IMPOSSIBLE_VERBOSE__ s

-- | Make sure a constructor is fully applied
--   and infer the type of the constructor.
--   Raises a type error if the constructor does not belong to the given type.
fullyApplyCon
  :: ConHead -- ^ Constructor.
  -> Elims    -- ^ Constructor arguments.
  -> Type    -- ^ Type of the constructor application.
  -> (QName -> Type -> Args -> Type -> Elims -> Telescope -> Type -> TCM a)
       -- ^ Name of the data/record type,
       --   type of the data/record type,
       --   reconstructed parameters,
       --   type of the constructor (applied to parameters),
       --   full application arguments,
       --   types of missing arguments (already added to context),
       --   type of the full application.
  -> TCM a
fullyApplyCon c vs t0 ret = do
  TelV tel t <- telView t0
  -- The type of the constructor application may still be a function
  -- type.  In this case, we introduce the domains @tel@ into the context
  -- and apply the constructor to these fresh variables.
  addContext tel $ do
    getFullyAppliedConType c t >>= \case
      Nothing ->
        typeError $ DoesNotConstructAnElementOf (conName c) t
      Just ((d, dt, pars), a) ->
        ret d dt pars a (raise (size tel) vs ++ map Apply (teleArgs tel)) tel t

checkSpine
  :: Action
  -> Type      -- ^ Type of the head @self@.
  -> Term      -- ^ The head @self@.
  -> Elims     -- ^ The eliminations @es@.
  -> Type      -- ^ Expected type of the application @self es@.
  -> TCM Term  -- ^ The application after modification by the @Action@.
checkSpine action a self es t = do
  reportSDoc "tc.check.internal" 20 $ sep
    [ "checking spine "
    , nest 2 $ sep [ parens (sep [ prettyTCM self <+> ":"
                                 , nest 2 $ prettyTCM a ])
                   , nest 4 $ prettyTCM es <+> ":"
                   , nest 2 $ prettyTCM t ] ]
  ((v, v'), t') <- inferSpine' action a self self es
  t' <- reduce t'
  v' <$ coerceSize subtype v t' t

checkArgs
  :: Action
  -> Type      -- ^ Type of the head.
  -> Term      -- ^ The head.
  -> Args      -- ^ The arguments.
  -> Type      -- ^ Expected type of the application.
  -> TCM Term  -- ^ The application after modification by the @Action@.
checkArgs action a self vs t = checkSpine action a self (map Apply vs) t

-- | @checkArgInfo actual expected@.
--
--   The @expected@ 'ArgInfo' comes from the type.
--   The @actual@ 'ArgInfo' comes from the term and can be updated
--   by an action.
checkArgInfo :: Action -> ArgInfo -> ArgInfo -> TCM ArgInfo
checkArgInfo action ai ai' = do
  checkHiding    (getHiding ai)     (getHiding ai')
  r <- checkRelevance action (getRelevance ai)  (getRelevance ai')
  return $ setRelevance r ai

checkHiding    :: Hiding -> Hiding -> TCM ()
checkHiding    h h' = unless (sameHiding h h') $ typeError $ HidingMismatch h h'

-- | @checkRelevance action term type@.
--
--   The @term@ 'Relevance' can be updated by the @action@.
checkRelevance :: Action -> Relevance -> Relevance -> TCM Relevance
checkRelevance action r r' = do
  unless (r == r') $ typeError $ RelevanceMismatch r r'
  return $ relevanceAction action r' r  -- Argument order for actions: @type@ @term@

-- | Infer type of a neutral term.
infer :: Term -> TCM Type
infer v = do
  case v of
    Var i es   -> do
      a <- typeOfBV i
      snd <$> inferSpine a (Var i   []) es
    Def f (Apply a : es) -> inferDef' f a es -- possibly proj.like
    Def f es             -> inferDef  f   es -- not a projection-like fun
    MetaV x es -> do -- we assume meta instantiations to be well-typed
      a <- metaType x
      snd <$> inferSpine a (MetaV x []) es
    _ -> __IMPOSSIBLE__

-- | Infer ordinary function application.
inferDef :: QName -> Elims -> TCM Type
inferDef f es = do
  a <- defType <$> getConstInfo f
  snd <$> inferSpine a (Def f []) es

-- | Infer possibly projection-like function application
inferDef' :: QName -> Arg Term -> Elims -> TCM Type
inferDef' f a es = do
  isProj <- isProjection f
  case isProj of
    Just Projection{ projIndex = n } | n > 0 -> do
      let self = unArg a
      b <- infer self
      snd <$> inferSpine b self (Proj ProjSystem f : es)
    _ -> inferDef f (Apply a : es)


-- | @inferSpine t self es@ checks that spine @es@ eliminates
--   value @self@ of type @t@ and returns the remaining type
--   (target of elimination) and the final self (has that type).
inferSpine :: Type -> Term -> Elims -> TCM (Term, Type)
inferSpine a v es = first fst <$> inferSpine' defaultAction a v v es

-- | Returns both the real term (first) and the transformed term (second). The
--   transformed term is not necessarily a valid term, so it must not be used
--   in types.
inferSpine' :: Action -> Type -> Term -> Term -> Elims -> TCM ((Term, Term), Type)
inferSpine' action t self self' [] = return ((self, self'), t)
inferSpine' action t self self' (e : es) = do
  reportSDoc "tc.infer.internal" 30 $ sep
    [ "inferSpine': "
    , "type t = " <+> prettyTCM t
    , "self  = " <+> prettyTCM self
    , "self' = " <+> prettyTCM self'
    , "eliminated by e = " <+> prettyTCM e
    ]
  case e of
    IApply x y r -> do
      (a, b) <- shouldBePath t
      r' <- checkInternal' action r (unDom a)
      izero <- primIZero
      ione  <- primIOne
      x' <- checkInternal' action x (b `absApp` izero)
      y' <- checkInternal' action y (b `absApp` ione)
      inferSpine' action (b `absApp` r) (self `applyE` [e]) (self' `applyE` [IApply x' y' r']) es
    Apply (Arg ai v) -> do
      (a, b) <- shouldBePi t
      ai <- checkArgInfo action ai $ domInfo a
      v' <- checkInternal' action v $ unDom a
      inferSpine' action (b `absApp` v) (self `applyE` [e]) (self' `applyE` [Apply (Arg ai v')]) es
    -- case: projection or projection-like
    Proj o f -> do
      (a, b) <- shouldBePi =<< shouldBeProjectible t f
      u  <- applyDef o f (argFromDom a $> self)
      u' <- applyDef o f (argFromDom a $> self')
      inferSpine' action (b `absApp` self) u u' es

-- | Type should either be a record type of a type eligible for
--   the principal argument of projection-like functions.
shouldBeProjectible :: Type -> QName -> TCM Type
-- shouldBeProjectible t f = maybe failure return =<< projectionType t f
shouldBeProjectible t f = maybe failure return =<< getDefType f =<< reduce t
  where failure = typeError $ ShouldBeRecordType t
    -- TODO: more accurate error that makes sense also for proj.-like funs.

shouldBePath :: Type -> TCM (Dom Type, Abs Type)
shouldBePath t = do
  m <- isPath t
  case m of
    Just p  -> return p
    Nothing -> typeError $ ShouldBePath t

shouldBePi :: Type -> TCM (Dom Type, Abs Type)
shouldBePi t = ifPiType t (\ a b -> return (a, b)) $ const $ typeError $ ShouldBePi t

-- | Result is in reduced form.
shouldBeSort :: Type -> TCM Sort
shouldBeSort t = ifIsSort t return (typeError $ ShouldBeASort t)

ifIsSort :: Type -> (Sort -> TCM a) -> TCM a -> TCM a
ifIsSort t yes no = do
  t <- reduce t
  case unEl t of
    Sort s -> yes s
    _      -> no

-- | Check if sort is well-formed.
checkSort :: Action -> Sort -> TCM Sort
checkSort action s =
  case s of
    Type l   -> Type <$> checkLevel action l
    Prop l   -> Prop <$> checkLevel action l
    Inf      -> return Inf
    SizeUniv -> return SizeUniv
    PiSort a b -> do
      a <- checkSort action a
      addContext (absName b, defaultDom (sort a) :: Dom Type) $ do
        PiSort a . Abs (absName b) <$> checkSort action (absBody b)
    UnivSort s -> UnivSort <$> checkSort action s
    MetaS x es -> do -- we assume sort meta instantiations to be well-formed
      a <- metaType x
      let self = Sort $ MetaS x []
      ((_,v),_) <- inferSpine' action a self self es
      case v of
        Sort s     -> return s
        MetaV x es -> return $ MetaS x es
        _          -> __IMPOSSIBLE__
    DummyS s -> __IMPOSSIBLE_VERBOSE__ s

-- | Check if level is well-formed.
checkLevel :: Action -> Level -> TCM Level
checkLevel action (Max ls) = Max <$> mapM checkPlusLevel ls
  where
    checkPlusLevel l@ClosedLevel{} = return l
    checkPlusLevel (Plus k l)      = Plus k <$> checkLevelAtom l

    checkLevelAtom l = do
      lvl <- levelType
      UnreducedLevel <$> case l of
        MetaLevel x es   -> checkInternal' action (MetaV x es) lvl
        BlockedLevel _ v -> checkInternal' action v lvl
        NeutralLevel _ v -> checkInternal' action v lvl
        UnreducedLevel v -> checkInternal' action v lvl

-- | Type of a term or sort meta.
metaType :: MetaId -> TCM Type
metaType x = jMetaType . mvJudgement <$> lookupMeta x

-- | Universe subsumption and type equality (subtyping for sizes, resp.).
subtype :: Type -> Type -> TCM ()
subtype t1 t2 = do
  ifIsSort t1 (\ s1 -> (s1 `leqSort`) =<< shouldBeSort t2) $ do
    -- Andreas, 2017-03-09, issue #2493
    -- Only check subtyping, do not solve any metas!
    -- TODO: NEED? disableDestructiveUpdate
    dontAssignMetas $ leqType t1 t2

-- | Compute the sort of a type.

inferSort :: Term -> TCM Sort
inferSort t = case t of
    Var i es   -> do
      a <- typeOfBV i
      (_, s) <- eliminate (Var i []) a es
      shouldBeSort s
    Def f es   -> do  -- f is not projection(-like)!
      a <- defType <$> getConstInfo f
      (_, s) <- eliminate (Def f []) a es
      shouldBeSort s
    MetaV x es -> do
      a <- metaType x
      (_, s) <- eliminate (MetaV x []) a es
      shouldBeSort s
    Pi a b     -> inferPiSort (getSort a) (getSort <$> b)
    Sort s     -> inferUnivSort s
    Con{}      -> __IMPOSSIBLE__
    Lit{}      -> __IMPOSSIBLE__
    Lam{}      -> __IMPOSSIBLE__
    Level{}    -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__
    Dummy s    -> __IMPOSSIBLE_VERBOSE__ s

-- | @eliminate t self es@ eliminates value @self@ of type @t@ by spine @es@
--   and returns the remaining value and its type.
eliminate :: Term -> Type -> Elims -> TCM (Term, Type)
eliminate self t [] = return (self, t)
eliminate self t (e : es) = case e of
    Apply (Arg _ v) -> ifNotPiType t __IMPOSSIBLE__ {-else-} $ \ _ b ->
      eliminate (self `applyE` [e]) (b `absApp` v) es
    IApply _ _ v -> do
      (_, b) <- shouldBePath t
      eliminate (self `applyE` [e]) (b `absApp` v) es
    -- case: projection or projection-like
    Proj o f -> do
      (Dom{domInfo = ai}, b) <- shouldBePi =<< shouldBeProjectible t f
      u  <- applyDef o f $ Arg ai self
      eliminate u (b `absApp` self) es
