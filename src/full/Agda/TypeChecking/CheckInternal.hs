{-# OPTIONS_GHC -Wunused-imports #-}

-- Initially authored by Andreas, 2013-10-22.

-- | A bidirectional type checker for internal syntax.
--
--   Performs checking on unreduced terms.
--   With the exception that projection-like function applications
--   have to be reduced since they break bidirectionality.

module Agda.TypeChecking.CheckInternal
  ( MonadCheckInternal
  , checkType, infer, inferSpine
  , CheckInternal(..)
  , Action(..), defaultAction, eraseUnusedAction
  ) where

import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty (prettyShow)

import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.ProjectionLike (elimView, ProjEliminator(..))
import Agda.TypeChecking.Polarity.Base
import Agda.TypeChecking.Records (shouldBeProjectible)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Telescope

import Agda.Utils.Function (applyWhen)
import Agda.Utils.Functor (($>))
import Agda.Utils.Maybe
import Agda.Utils.Size

import Agda.Utils.Impossible

import Agda.Interaction.Options

-- * Bidirectional rechecker

type MonadCheckInternal m = MonadConversion m

{-# SPECIALIZE checkType :: Type -> TCM () #-}
-- | Entry point for e.g. checking WithFunctionType.
checkType :: (MonadCheckInternal m) => Type -> m ()
checkType t = catchConstraint (CheckType t) $ inferInternal t

-- | 'checkInternal' traverses the whole 'Term', and we can use this
--   traversal to modify the term.
data Action m = Action
  { preAction  :: Type -> Term -> m Term
    -- ^ Called on each subterm before the checker runs.
  , postAction :: Type -> Term -> m Term
    -- ^ Called on each subterm after the type checking.
  , modalityAction :: Modality -> Modality -> Modality
    -- ^ Called for each @ArgInfo@.
    --   The first 'Modality' is from the type,
    --   the second from the term.
  , elimViewAction :: Term -> m Term
    -- ^ Called for bringing projection-like funs in post-fix form
  }

-- | The default action is to not change the 'Term' at all.
defaultAction :: PureTCM m => Action m
--(MonadReduce m, MonadTCEnv m, HasConstInfo m) => Action m
defaultAction = Action
  { preAction       = \ _ -> return
  , postAction      = \ _ -> return
  , modalityAction  = \ _ -> id
  , elimViewAction  = elimView EvenLone
  }

eraseUnusedAction :: Action TCM
eraseUnusedAction = defaultAction { postAction = eraseUnused }
  where
    eraseUnused :: Type -> Term -> TCM Term
    eraseUnused t = \case
      Def f es -> do
        pols <- getPolarity f
        return $ Def f $ eraseIfNonvariant pols es
      v        -> return v

    eraseIfNonvariant :: [Polarity] -> Elims -> Elims
    eraseIfNonvariant []                  es             = es
    eraseIfNonvariant pols                []             = []
    eraseIfNonvariant (Nonvariant : pols) (e : es) = (fmap dontCare e) : eraseIfNonvariant pols es
    eraseIfNonvariant (_          : pols) (e : es) = e : eraseIfNonvariant pols es

class CheckInternal a where
  checkInternal' :: (MonadCheckInternal m) => Action m -> a -> Comparison -> TypeOf a -> m a

  checkInternal :: (MonadCheckInternal m) => a -> Comparison -> TypeOf a -> m ()
  checkInternal v cmp t = void $ checkInternal' defaultAction v cmp t

  inferInternal' :: (MonadCheckInternal m, TypeOf a ~ ()) => Action m -> a -> m a
  inferInternal' act v = checkInternal' act v CmpEq ()

  inferInternal :: (MonadCheckInternal m, TypeOf a ~ ()) => a -> m ()
  inferInternal v = checkInternal v CmpEq ()

{-# SPECIALIZE checkInternal' :: Action TCM -> Term  -> Comparison -> TypeOf Term -> TCM Term #-}
{-# SPECIALIZE checkInternal' :: Action TCM -> Type  -> Comparison -> TypeOf Type -> TCM Type #-}
{-# SPECIALIZE checkInternal' :: Action TCM -> Elims -> Comparison -> TypeOf Type -> TCM Elims #-}
{-# SPECIALIZE checkInternal  :: Term -> Comparison -> TypeOf Term -> TCM () #-}
{-# SPECIALIZE checkInternal  :: Type -> Comparison -> TypeOf Type -> TCM () #-}

instance CheckInternal Type where
  checkInternal' action (El s t) cmp _ = do
    t' <- checkInternal' action t cmp (sort s)
    s' <- sortOf t'
    compareSort cmp s' s
    return (El s t')

instance CheckInternal Term where
  checkInternal' :: (MonadCheckInternal m) => Action m -> Term -> Comparison -> Type -> m Term
  checkInternal' action v cmp t = verboseBracket "tc.check.internal" 20 "" $ do
    reportSDoc "tc.check.internal" 20 $ sep
      [ "checking internal "
      , nest 2 $ sep [ prettyTCM v <+> ":"
                    , nest 2 $ prettyTCM t ] ]
    reportSDoc "tc.check.internal" 60 $ sep
      [ "checking internal with DB indices"
      , nest 2 $ sep [ pretty v <+> ":"
                    , nest 2 $ pretty t ] ]
    ctx <- getContextTelescope
    unless (null ctx) $ reportSDoc "tc.check.internal" 30 $ sep
      [ "In context"
      , nest 2 $ sep [ prettyTCM ctx ] ]
    -- Bring projection-like funs in post-fix form,
    -- (even lone ones by default).
    v <- elimViewAction action =<< preAction action t v
    postAction action t =<< case v of
      Var i es   -> do
        d <- domOfBV i
        n <- nameOfBV i

        -- Lucas, 23-11-2022:
        -- For now we only check if pure modalities are respected.
        -- In the future we SHOULD also be doing the same checks for every modality, as in Rules/Applications.hs
        -- (commented below)
        -- but this will break stuff that is allowed right now

        unless (usableCohesion d) $
          typeError $ VariableIsOfUnusableCohesion n (getCohesion d)

        reportSDoc "tc.check.internal" 30 $ fsep
          [ "variable" , prettyTCM (var i) , "has type" , prettyTCM (unDom d)
          , "and modality", pretty (getModality d) ]
        checkSpine action (unDom d) (Var i) es cmp t
      Def f es   -> do  -- f is not projection(-like)!
        -- There is no "implicitely applied module telescope" at this stage, so no
        -- need to check it for modal errors, everything is covered by the
        -- variable rule!
        a <- defType <$> getConstInfo f
        checkSpine action a (Def f) es cmp t
      MetaV x es -> do -- we assume meta instantiations to be well-typed
        a <- metaType x
        reportSDoc "tc.check.internal" 30 $ "metavariable" <+> prettyTCM x <+> "has type" <+> prettyTCM a
        checkSpine action a (MetaV x) es cmp t
      Con c ci vs -> do
        -- We need to fully apply the constructor to make getConType work!
        fullyApplyCon c vs t $ \ _d _dt _pars a vs' tel t -> do
          Con c ci vs2 <- checkSpine action a (Con c ci) vs' cmp t
          -- Strip away the extra arguments
          return $ applySubst (strengthenS impossible (size tel))
            $ Con c ci $ take (length vs) vs2
      Lit l      -> do
        lt <- litType l
        compareType cmp lt t
        return $ Lit l
      Lam ai vb  -> do
        (a, b) <- shouldBePiOrPath t
        ai <- checkArgInfo action ai $ domInfo a
        let name = suggests [ Suggestion vb , Suggestion b ]
        addContext (name, a) $ do
          Lam ai . Abs (absName vb) <$> checkInternal' action (absBody vb) cmp (absBody b)
      Pi a b     -> do
        s <- shouldBeSort t
        reportSDoc "tc.check.internal" 30 $ "pi type should have sort" <+> prettyTCM s
        when (s == SizeUniv) $ typeError $ FunctionTypeInSizeUniv v
        experimental <- optExperimentalIrrelevance <$> pragmaOptions
        let sa  = getSort a
            sb  = getSort (unAbs b)
            mkDom v = El sa v <$ a
            mkRng v = fmap (v <$) b
            -- Preserve NoAbs
            goInside = case b of
              Abs{}   -> addContext $ (absName b,) $
                applyWhen experimental (mapRelevance irrToNonStrict) a
              NoAbs{} -> id
        a <- mkDom <$> checkInternal' action (unEl $ unDom a) CmpLeq (sort sa)
        v' <- goInside $ Pi a . mkRng <$> checkInternal' action (unEl $ unAbs b) CmpLeq (sort sb)
        s' <- sortOf v -- Issue #6205: do not use v' since it might not be valid syntax
        compareSort cmp s' s
        return v'
      Sort s     -> do
        reportSDoc "tc.check.internal" 30 $ "checking sort" <+> prettyTCM s
        s <- inferInternal' action s
        s' <- inferUnivSort s
        s'' <- shouldBeSort t
        compareSort cmp s' s''
        return $ Sort s
      Level l    -> do
        l <- inferInternal' action l
        lt <- levelType'
        compareType cmp lt t
        return $ Level l
      DontCare v -> DontCare <$> checkInternal' action v cmp t
      -- Jesper, 2023-02-23: these can appear because of eta-expansion of
      -- records with irrelevant fields
      Dummy s _ -> return v -- __IMPOSSIBLE_VERBOSE__ s

-- | @checkArgInfo actual expected@.
--
--   The @expected@ 'ArgInfo' comes from the type.
--   The @actual@ 'ArgInfo' comes from the term and can be updated
--   by an action.
checkArgInfo :: (MonadCheckInternal m) => Action m -> ArgInfo -> ArgInfo -> m ArgInfo
checkArgInfo action ai ai' = do
  checkHiding    (getHiding ai)     (getHiding ai')
  mod <- checkModality action (getModality ai)  (getModality ai')
  return $ setModality mod ai

checkHiding :: (MonadCheckInternal m) => Hiding -> Hiding -> m ()
checkHiding h h' = unless (sameHiding h h') $ typeError $ HidingMismatch h h'

-- | @checkRelevance action term type@.
--
--   The @term@ 'Relevance' can be updated by the @action@.
checkModality :: (MonadCheckInternal m) => Action m -> Modality -> Modality -> m Modality
checkModality action mod mod' = do
  let (r,r') = (getRelevance mod, getRelevance mod')
      (q,q') = (getQuantity  mod, getQuantity  mod')
  unless (sameModality mod mod') $ typeError $ if
    | not (sameRelevance r r') -> RelevanceMismatch r r'
    | not (sameQuantity q q')  -> QuantityMismatch  q q'
    | otherwise -> __IMPOSSIBLE__ -- add more cases when adding new modalities
  return $ modalityAction action mod' mod  -- Argument order for actions: @type@ @term@

{-# SPECIALIZE infer :: Term -> TCM Type #-}
-- | Infer type of a neutral term.
infer :: (MonadCheckInternal m) => Term -> m Type
infer u = do
  reportSDoc "tc.check.internal" 20 $ "CheckInternal.infer" <+> prettyTCM u
  case u of
    Var i es -> do
      a <- typeOfBV i
      fst <$> inferSpine defaultAction a (Var i) es
    Def f es -> do
      whenJustM (isRelevantProjection f) $ \_ -> nonInferable
      a <- defType <$> getConstInfo f
      fst <$> inferSpine defaultAction a (Def f) es
    MetaV x es -> do -- we assume meta instantiations to be well-typed
      a <- metaType x
      fst <$> inferSpine defaultAction a (MetaV x) es
    _ -> nonInferable
  where
    nonInferable :: MonadDebug m => m a
    nonInferable = __IMPOSSIBLE_VERBOSE__ $ unlines
      [ "CheckInternal.infer: non-inferable term:"
      , "  " ++ prettyShow u
      ]

instance CheckInternal Elims where
  checkInternal' action es cmp (t , hd) = snd <$> inferSpine action t hd es

{-# SPECIALIZE inferSpine :: Action TCM -> Type -> (Elims -> Term) -> Elims -> TCM (Type, Elims) #-}
-- | @inferSpine action t hd es@ checks that spine @es@ eliminates
--   value @hd []@ of type @t@ and returns the remaining type
--   (target of elimination) and the transformed eliminations.
inferSpine :: (MonadCheckInternal m) => Action m -> Type -> (Elims -> Term) -> Elims -> m (Type, Elims)
inferSpine action t hd es = loop t hd id es
  where
  loop t hd acc = \case
    [] -> return (t , acc [])
    (e : es) -> do
      let self = hd []
      reportSDoc "tc.check.internal" 30 $ sep
        [ "inferring spine: "
        , "type t = " <+> prettyTCM t
        , "self  = " <+> prettyTCM self
        , "eliminated by e = " <+> prettyTCM e
        ]
      case e of
        IApply x y r -> do
          (a, b) <- shouldBePath t
          r' <- checkInternal' action r CmpLeq (unDom a)
          izero <- primIZero
          ione  <- primIOne
          x' <- checkInternal' action x CmpLeq (b `absApp` izero)
          y' <- checkInternal' action y CmpLeq (b `absApp` ione)
          let e' = IApply x' y' r'
          loop (b `absApp` r) (hd . (e:)) (acc . (e':)) es
        Apply (Arg ai v) -> do
          (a, b) <- shouldBePi t
          ai <- checkArgInfo action ai $ domInfo a
          v' <- applyModalityToContext (getModality a) $ checkInternal' action v CmpLeq $ unDom a
          let e' = Apply (Arg ai v')
          loop (b `absApp` v) (hd . (e:)) (acc . (e':)) es
        -- case: projection or projection-like
        Proj o f -> do
          t' <- shouldBeProjectible self t o f
          loop t' (hd . (e:)) (acc . (e:)) es

{-# SPECIALIZE checkSpine :: Action TCM -> Type -> (Elims -> Term) -> Elims -> Comparison -> Type -> TCM Term #-}
checkSpine
  :: (MonadCheckInternal m)
  => Action m
  -> Type       -- ^ Type of the head @self@.
  -> (Elims -> Term) -- ^ The head @hd@.
  -> Elims      -- ^ The eliminations @es@.
  -> Comparison -- ^ Check (@CmpLeq@) or infer (@CmpEq@) the final type.
  -> Type       -- ^ Expected type of the application @self es@.
  -> m Term     -- ^ The application after modification by the @Action@.
checkSpine action a hd es cmp t = do
  reportSDoc "tc.check.internal" 20 $ sep
    [ "checking spine "
    , nest 2 $ sep [ parens (sep [ prettyTCM (hd []) <+> ":"
                                 , nest 2 $ prettyTCM a ])
                   , nest 4 $ prettyTCM es <+> ":"
                   , nest 2 $ prettyTCM t ] ]
  (t' , es') <- inferSpine action a hd es
  coerceSize (compareType cmp) (hd es) t' t
  return $ hd es'

instance CheckInternal Sort where
  checkInternal' action s cmp _ = case s of
    Univ u l -> Univ u <$> inferInternal' action l
    Inf u n  -> return $ Inf u n
    SizeUniv -> return SizeUniv
    LockUniv -> return LockUniv
    LevelUniv -> return LevelUniv
    IntervalUniv -> return IntervalUniv
    PiSort dom s1 s2 -> do
      let a = unDom dom
      s1' <- inferInternal' action s1
      a' <- checkInternal' action a CmpLeq $ sort s1'
      let dom' = dom $> a'
      s2' <- mapAbstraction (El s1' <$> dom') (inferInternal' action) s2
      return $ PiSort dom' s1' s2'
    FunSort s1 s2 -> do
      s1' <- inferInternal' action s1
      s2' <- inferInternal' action s2
      return $ FunSort s1' s2'
    UnivSort s -> UnivSort <$> inferInternal' action s
    MetaS x es -> do -- we assume sort meta instantiations to be well-formed
      a <- metaType x
      MetaS x <$> checkInternal' action es cmp (a , Sort . MetaS x)
    DefS d es -> do
      a <- defType <$> getConstInfo d
      DefS d <$> checkInternal' action es cmp (a , Sort . DefS d)
    DummyS s -> __IMPOSSIBLE_VERBOSE__ s

instance CheckInternal Level where
  checkInternal' action (Max n ls) _ _ = Max n <$> mapM (inferInternal' action) ls

instance CheckInternal PlusLevel where
  checkInternal' action (Plus k l) _ _ = Plus k <$> checkLevelAtom l
    where
    checkLevelAtom l = do
      lvl <- levelType'
      checkInternal' action l CmpLeq lvl
