        {-# LANGUAGE OverloadedStrings #-}
module Check (checkProgram) where

import           Prelude                          hiding (abs, pi)

import           Data.Functor                     ((<$>), (<$))
import           Data.Foldable                    (foldMap, forM_)
import           Data.Monoid                      (Monoid(..),(<>))
import qualified Data.HashSet                     as HS
import           Control.Monad                    (when, void)
import           Data.List                        (nub)
import           Data.Traversable                 (traverse, sequenceA)
import           Prelude.Extras                   ((==#))
import           Bound                            hiding (instantiate, abstract)
import           Bound.Var                        (unvar)
import qualified Bound.Name                       as Bound
import           Data.Maybe                       (maybeToList)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (vacuous, Void, vacuousM)
import qualified Data.Set                         as Set
import qualified Data.Map                         as Map
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Either       (EitherT(EitherT), runEitherT)

import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import qualified Syntax.Abstract                  as A
import           Types.Definition
import qualified Types.Context                    as Ctx
import qualified Types.Telescope                  as Tel
import           Types.Monad
import           Types.Term
import           Types.Var
import           Text.PrettyPrint.Extended        (render, (<+>), ($$))
import qualified Text.PrettyPrint.Extended        as PP
import qualified Types.Signature                  as Sig
import           Eval

-- Main functions
------------------------------------------------------------------------

-- Type checking
----------------

check :: (IsVar v, IsTerm t) => A.Expr -> Type t v -> TC t v (Term t v)
check synT type_ = atSrcLoc synT $ case synT of
  A.Con dataCon synArgs -> do
    Constructor tyCon dataConType <- getDefinition dataCon
    let err = ConstructorTypeError synT type_
    metaVarIfStuck type_ $ matchTyCon tyCon type_ err $ \tyConArgs -> do
      let appliedDataConType = Tel.substs (vacuous dataConType) tyConArgs
      bindStuckTC (checkConArgs synArgs appliedDataConType) WaitingOn $ \args ->
        notStuck $ con dataCon args
  A.Refl _ -> do
    let err = NotEqualityType type_
    metaVarIfStuck type_ $ matchEqual type_ err  $ \type' t1 t2 -> do
      bindStuckTC (checkEqual type' t1 t2) WaitingOn $ \() ->
        notStuck refl
  A.Meta _ ->
    addMetaVarInCtx type_
  A.Lam name synBody -> do
    let err = LambdaTypeError synT type_
    metaVarIfStuck type_ $ matchPi name type_ err  $ \dom cod -> do
      body <- extendContext name dom $ \_ -> check synBody (fromAbs cod)
      notStuck $ lam (toAbs body)
  _ -> do
    stuck <- infer synT
    -- TODO Use combinators below, remove duplication with
    -- `metaVarIfStuck'.
    case stuck of
      NotStuck (t, type') -> do
        stuck' <- equalType type_ type'
        case stuck' of
          NotStuck () -> do
            return t
          StuckOn pid -> do
            mv <- addMetaVarInCtx type_
            void $ waitOnProblemCheckEqual pid type' mv t
            return mv
      StuckOn pid -> do
        mv <- addMetaVarInCtx type_
        void $ bindProblem pid (WaitForInfer synT type_) $ \(t, type') -> do
          stuck' <- equalType type_ type'
          case stuck' of
            NotStuck () ->
              checkEqual type_ mv t
            StuckOn pid' ->
              StuckOn <$> waitOnProblemCheckEqual pid' type_ mv t
        return mv

isType :: (IsVar v, IsTerm t) => A.Expr -> TC t v (Type t v)
isType abs = check abs set

checkConArgs :: (IsVar v, IsTerm t) => [A.Expr] -> Type t v -> StuckTC t v [t v]
checkConArgs []                 _     = notStuck []
checkConArgs (synArg : synArgs) type_ = atSrcLoc synArg $ do
  let err = ExpectedFunctionType type_ (Just synArg)
  matchPi_ type_ err $ \dom cod -> do
    arg <- check synArg dom
    bindStuckTC (checkConArgs synArgs (instantiate cod arg)) WaitingOn $ \args ->
      notStuck (arg : args)

infer :: (IsVar v, IsTerm t) => A.Expr -> StuckTC t v (Term t v, Type t v)
infer synT = atSrcLoc synT $ case synT of
  A.Set _ ->
    notStuck (set, set)
  A.Pi name synDomain synCodomain -> do
    domain   <- isType synDomain
    codomain <- extendContext name domain $ \_ -> isType synCodomain
    notStuck (pi domain (toAbs codomain), set)
  A.Fun synDomain synCodomain -> do
    domain   <- isType synDomain
    codomain <- isType synCodomain
    notStuck (pi domain (weaken codomain), set)
  A.App synH elims -> do
    (h, type_) <- inferHead synH
    checkSpine (unview (App h [])) elims type_
  A.Equal synType synX synY -> do
    type_ <- isType synType
    x <- check synX type_
    y <- check synY type_
    notStuck (equal type_ x y, set)
  _ -> do
    type_ <- addMetaVarInCtx set
    t <- check synT type_
    notStuck (t, type_)

checkSpine :: (IsVar v, IsTerm t)
           => Term t v -> [A.Elim] -> Type t v -> StuckTC t v (Term t v, Type t v)
checkSpine h []         type_ = notStuck (h, type_)
checkSpine h (el : els) type_ = atSrcLoc el $ case el of
  A.Proj proj -> do
    bindStuckTC (applyProjection proj h type_) (\_ -> CheckSpine h (el :els) type_) $
      \(h', type') -> checkSpine h' els type'
  A.Apply synArg -> do
    let err = ExpectedFunctionType type_ (Just synArg)
    matchPi_ type_ err $ \dom cod -> do
      arg <- check synArg dom
      let cod' = instantiate cod arg
      let h' = eliminate h [Apply arg]
      checkSpine h' els cod'

inferHead :: (IsVar v, IsTerm t) => A.Head -> TC t v (Head v, Type t v)
inferHead synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    mbType <- getTypeOfName name
    case mbType of
      Nothing         -> checkError $ NameNotInScope name
      Just (v, type_) -> return (Var v, type_)
  A.Def name -> do
    type_ <- definitionType <$> getDefinition name
    return (Def name, vacuous type_)
  A.J{} ->
    return (J, vacuous $ typeOfJ)

-- Equality
-----------

checkEqual :: (IsVar v, IsTerm t) => Type t v -> Term t v -> Term t v -> StuckTC t v ()
checkEqual _ x y | x ==# y =
  notStuck ()
checkEqual type_ x y = do
  typeView <- whnfViewTC type_
  expand <- etaExpand typeView
  blockedX <- whnfTC $ expand x
  blockedY <- whnfTC $ expand y
  case (blockedX, blockedY) of
    (_, _) | blockedX ==# blockedY ->
      notStuck ()
    (MetaVarHead mv elims, t) ->
      metaAssign type_ mv elims (ignoreBlocking t)
    (t, MetaVarHead mv elims) ->
      metaAssign type_ mv elims (ignoreBlocking t)
    (BlockedOn mvs _ _, _) -> do
      fmap StuckOn $
        newProblemCheckEqual mvs (unview typeView)
                             (ignoreBlocking blockedX) (ignoreBlocking blockedY)
    (_, BlockedOn mvs _ _) -> do
      fmap StuckOn $
        newProblemCheckEqual mvs (unview typeView)
                             (ignoreBlocking blockedX) (ignoreBlocking blockedY)
    (NotBlocked x', NotBlocked y') -> case (typeView, view x', view y') of
      -- Note that here we rely on canonical terms to have canonical
      -- types, and on the terms to be eta-expanded.
      (Pi dom cod, Lam body1, Lam body2) -> do
        -- TODO there is a bit of duplication between here and expansion.
        let body1' = fromAbs body1
        let body2' = fromAbs body2
        let cod'   = fromAbs cod
        -- This is unfortunate, we need to create a new problem only
        -- because the recursive call is in a different context.
        stuck <- extendContext (getName_ body1') dom $ \_ ->
                 checkEqual cod' body1' body2'
        -- TODO use some helper function
        case stuck of
          NotStuck () ->
            notStuck ()
          StuckOn pid ->
            StuckOn <$> waitOnProblem pid (EscapingScope pid) (notStuck ())
      (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
        let cod1' = fromAbs cod1
        stuck <- checkEqual set dom1 dom2
        -- TODO use some helper function for the various `waitOnProblem'
        -- (see above)
        case stuck of
          NotStuck () -> do
            stuck' <- extendContext (getName_ cod1') dom1 $ \_ ->
              checkEqual set cod1' (fromAbs cod2)
            case stuck' of
              NotStuck () -> notStuck ()
              StuckOn pid -> StuckOn <$> waitOnProblem pid (EscapingScope pid) (notStuck ())
          StuckOn pid -> do
            pid' <- extendContext (getName_ cod1') dom1 $ \_ ->
                    waitOnProblemCheckEqual pid set cod1' (fromAbs cod2)
            StuckOn <$> waitOnProblem pid' (EscapingScope pid') (notStuck ())
      (Set, Equal type1 x1 y1, Equal type2 x2 y2) ->
        bindStuckTC (checkEqual set type1 type2) (\_ -> CheckEqual type1 x1 x2) $ \() ->
        bindStuckTC (checkEqual type1 x1 x2)     (\_ -> CheckEqual type1 y1 y2) $ \() ->
        checkEqual type1 y1 y2
      (_, Refl, Refl) -> do
        notStuck ()
      (App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2)
          | Just tyConPars <- mapM isApply tyConPars0
          , dataCon == dataCon' -> do
            Constructor _ dataConType <- getDefinition dataCon
            let appliedDataConType = Tel.substs (vacuous dataConType) tyConPars
            equalConArgs appliedDataConType dataCon dataConArgs1 dataConArgs2
      (Set, Set, Set) -> do
        notStuck ()
      (_, App h1 elims1, App h2 elims2) | h1 == h2 -> do
        h1Type <- case h1 of
          Var v   -> getTypeOfVar v
          Def f   -> vacuous . definitionType <$> getDefinition f
          J       -> return $ vacuous typeOfJ
          Meta _  -> error "impossible.checkEqual: can't decompose with metavariable heads"
        equalSpine h1Type (app h1 []) elims1 elims2
      (_, _, _) -> do
        checkError $ TermsNotEqual x y
  where
    etaExpand typeView = do
      sig <- getSignature
      case typeView of
        App (Def tyCon) _ | isRecordType sig tyCon -> do
          let Constant (Record dataCon projs) _ = Sig.getDefinition sig tyCon
          return $ \t ->
            def dataCon $ map (\(n, ix) -> Apply (eliminate t [Proj n ix])) projs
        Pi _ codomain -> do
          let name = getName_ $ fromAbs codomain
          let v    = var $ boundTermVar name
          return $ \t ->
            case view t of
              Lam _ -> t
              _     -> lam $ toAbs $ eliminate (fromAbs (weaken t)) [Apply v]
        _ ->
          return id

equalType :: (IsVar v, IsTerm t) => Type t v -> Type t v -> StuckTC t v ()
equalType a b = checkEqual set a b

equalSpine
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type of the head.
    -> Term t v
    -- ^ Head.
    -> [Elim (Term t) v]
    -> [Elim (Term t) v]
    -> StuckTC t v ()
equalSpine _ _ [] [] =
  notStuck ()
equalSpine type_ h (elim1 : elims1) (elim2 : elims2) = do
  let desc = EqualSpine h (elim1 : elims1) (elim2 : elims2) type_
  case (elim1, elim2) of
    (Apply arg1, Apply arg2) -> do
      typeView <- whnfViewTC type_
      case typeView of
        Pi domain codomain -> do
          bindStuckTC (checkEqual domain arg1 arg2) (\_ -> desc) $ \() ->
            equalSpine (instantiate codomain arg1) (eliminate h [Apply arg1]) elims1 elims2
        _ ->
          error $ "impossible.equalSpine: Expected function type " ++ render typeView
    (Proj proj projIx, Proj proj' projIx')
      | proj == proj' && projIx == projIx' ->
        bindStuckTC (applyProjection proj h type_) (\_ -> desc) $ \(h', type') ->
          equalSpine type' h' elims1 elims2
    _ ->
      checkError $ SpineNotEqual type_ (elim1 : elims1) (elim1 : elims2)
equalSpine type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 elims2

-- | INVARIANT: the two lists are the of the same length.
equalConArgs
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type of the head.
    -> Name -> [Term t v] -> [Term t v] -> StuckTC t v ()
equalConArgs type_ dataCon xs ys = do
  expandedCon <- unrollPi type_ $ \ctx _ ->
                 return $ ctxLam ctx $ con dataCon $ map var $ ctxVars ctx
  equalSpine type_ expandedCon (map Apply xs) (map Apply ys)

applyProjection
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Name of the projection
    -> Term t v
    -- ^ Head
    -> Type t v
    -- ^ Type of the head
    -> StuckTC t v (Term t v, Type t v)
applyProjection proj h type_ = do
  projDef <- getDefinition proj
  case projDef of
    Projection projIx tyCon projType -> do
      let h' = eliminate h [Proj proj projIx]
      let err = ExpectingRecordType type_
      matchTyCon tyCon type_ err $ \tyConArgs -> fmap NotStuck $ do
        let appliedProjType = view $ Tel.substs (vacuous projType) tyConArgs
        case appliedProjType of
          Pi _ endType ->
            return (h', instantiate endType h)
          _ ->
            error $ "impossible.applyProjection: " ++ render appliedProjType
    _ ->
      error $ "impossible.applyProjection: " ++ render projDef

-- MetaVar handling
-------------------

addMetaVarInCtx :: (IsTerm t) => Type t v -> TC t v (Term t v)
addMetaVarInCtx type_ = do
  ctx <- askContext
  mv <- addMetaVar $ ctxPi ctx type_
  return $ ctxApp (metaVar mv []) ctx

createTyConParsMvs :: (IsTerm t) => Tel.IdTel (Type t) v -> TC t v [Term t v]
createTyConParsMvs (Tel.Empty _) =
  return []
createTyConParsMvs (Tel.Cons (name, type') tel) = do
  mv  <- addMetaVarInCtx type'
  mvs <- extendContext name type' $ \_ -> createTyConParsMvs tel
  return (mv : map (\t -> instantiate (toAbs t) mv) mvs)

metaAssign
    :: (IsVar v, IsTerm t)
    => Type t v -> MetaVar -> [Elim (Term t) v] -> Term t v -> StuckTC t v ()
metaAssign type_ mv elims t = do
  vsOrMvs <- checkPatternCondition elims
  case vsOrMvs of
    Left mvs -> do
      -- If the pattern condition is not respected and we can't wait on
      -- any metavariable to make progress, we try to prune the
      -- metavariable
      sig <- getSignature
      let t' = nf sig t
      vs <- liftClosed $ rigidVars t'
      pruned <- liftClosed $ prune (`elem` vs) mv $ map (nf' sig) elims
      if pruned
        then checkEqual type_ (metaVar mv elims) t
        else fmap StuckOn $
               newProblem (Set.insert mv mvs) (CheckEqual type_ (metaVar mv elims) t) $ \mvT ->
                 checkEqual type_ (eliminate (vacuous mvT) elims) t
    Right vs -> do
      -- TODO have `pruneTerm' return an evaluated term.
      liftClosed $ pruneTerm vs t
      sig <- getSignature
      res <- closeTerm $ lambdaAbstract vs $ nf sig t
      case res of
        Closed t' -> do
          let mvs = metaVars t'
          when (mv `HS.member` mvs) $ checkError $ OccursCheckFailed mv $ vacuous t'
          instantiateMetaVar mv t'
          notStuck ()
        FlexibleOn mvs ->
          fmap StuckOn $
            newProblemCheckEqual (Set.insert mv mvs) type_ (metaVar mv elims) t
        Rigid v ->
          checkError $ FreeVariableInEquatedTerm mv elims t v

-- | The term must be in normal form.
pruneTerm
    :: (IsVar v, IsTerm t)
    => [v]                      -- ^ allowed vars
    -> Term t v
    -> ClosedTC t ()
pruneTerm vs t = do
  sig <- getSignature
  case whnfView sig t of
    Lam body -> do
      let body' = fromAbs body
      pruneTerm (boundTermVar (getName_ body') : map F vs) body'
    Pi domain codomain -> do
      pruneTerm vs domain
      let codomain' = fromAbs codomain
      pruneTerm (boundTermVar (getName_ codomain') : map F vs) codomain'
    Equal type_ x y ->
      mapM_ (pruneTerm vs) [type_, x, y]
    App (Meta mv) elims ->
      void (liftClosed (prune (`elem` vs) mv elims)) >> return ()
    App _ elims ->
      mapM_ (pruneTerm vs) [t' | Apply t' <- elims]
    Set ->
      return ()
    Refl ->
      return ()
    Con _ args ->
      mapM_ (pruneTerm vs) args

-- | Prunes a 'MetaVar' application and instantiates the new body.
-- Returns whether some pruning was performed.
--
-- The term must be in normal form.
prune
    :: forall t v0.
       (IsVar v0, IsTerm t)
    => (v0 -> Bool)             -- ^ allowed vars
    -> MetaVar
    -> [Elim (Term t) v0]       -- ^ Arguments to the metavariable
    -> ClosedTC t Bool
prune allowedVar oldMv elims | Just args <- mapM isApply elims = do
  argsMatchable <- mapM potentiallyMatchable args
  if or argsMatchable
    then return False
    else do
      -- TODO check that newly created meta is well-typed.
      kills0 <- mapM toKill args
      oldMvType <- getTypeOfMetaVar oldMv
      (newMvType, kills1) <- createNewMeta oldMvType kills0
      newMv <- addMetaVar $ telPi newMvType
      if any (\(Bound.Name _ b) -> b) kills1
        then True <$ instantiateMetaVar oldMv (createMetaLam newMv kills1)
        else return False
  where
    toKill arg = not . all allowedVar <$> rigidVars arg

    -- We build a telescope with only the non-killed types in.  This
    -- way, we can analyze the dependency between arguments and avoid
    -- killing things that later arguments depend on.
    --
    -- At the end of the telescope we put both the new metavariable and
    -- the remaining type, so that this dependency check will be
    -- performed on it as well.
    createNewMeta
      :: Type t v -> [Bool]
      -> TC t v (Tel.IdTel (Type t) v, [Named Bool])
    createNewMeta type_ [] = do
      return (Tel.Empty (Tel.Id type_), [])
    createNewMeta type_ (kill : kills) = do
      typeView <- whnfViewTC type_
      case typeView of
        Pi domain codomain -> do
          let codomain' = fromAbs codomain
          let name      = getName_ codomain'
          (tel, kills') <-
            extendContext name domain $ \_ -> createNewMeta codomain' kills
          let notKilled = (Tel.Cons (name, domain) tel, named name False : kills')
          return $
            if not kill
            then notKilled
            else case traverse (unvar (const Nothing) Just) tel of
              Nothing   -> notKilled
              Just tel' -> (tel', named name True : kills')
        _ ->
          error "impossible.createPrunedMeta: metavar type too short"

    createMetaLam :: MetaVar -> [Named Bool] -> Closed (Type t)
    createMetaLam newMv = go []
      where
        go :: [v] -> [Named Bool] -> Type t v
        go vs [] =
          metaVar newMv $ map (Apply . var) (reverse vs)
        go vs (kill : kills) =
          let vs' = (if unNamed kill then [] else [B (() <$ kill)]) ++ map F vs
          in lam $ toAbs $ go vs' kills
prune _ _ _ = do
  -- TODO we could probably do something more.
  return False

-- | Collects all the rigidly occurring variables in a term.
--
-- With "rigidly occurring" we mean everything which is not flexibly
-- occurring.
--
-- With "flexible occurring" here we mean either occurring as an
-- argument of a metavariable or an argument of an object variable that
-- might be substituted with a metavariable.
--
-- Note that we don't specify how precise the detection of said
-- "substitutable" object variables is we might be more conservative
-- than possible.
rigidVars
    :: forall t v0.
       (IsVar v0, IsTerm t)
    => Term t v0 -> ClosedTC t [v0]
rigidVars t0 = do
  sig <- getSignature
  let
    go :: (IsVar v)
       => (v -> Maybe v0)
       -> (v -> Bool)
       -- ^ vars that count as flexible, and so also flexible contexts
       -> Term t v -> [v0]
    go strengthen flex t =
      case whnfView sig t of
        Lam body ->
          go (lift' strengthen) (addNew flex) (fromAbs body)
          -- addNew is conservative, some lambdas might not be reachable
        Pi domain codomain ->
          go strengthen flex domain <>
          go (lift' strengthen) (ignoreNew flex) (fromAbs codomain)
        Equal type_ x y ->
          foldMap (go strengthen flex) [type_, x, y]
        App (Var v) elims ->
          if flex v
          then mempty
          else maybeToList (strengthen v) <>
               foldMap (go strengthen flex) [t' | Apply t' <- elims]
        App (Def d) elims ->
          if isNeutral sig d elims
          then foldMap (go strengthen flex) [t' | Apply t' <- elims]
          else mempty
        App J elims ->
          foldMap (go strengthen flex) [t' | Apply t' <- elims]
        App (Meta _) _ ->
          mempty
        Set ->
          mempty
        Refl ->
          mempty
        Con _ _ ->
          mempty
          -- conservative, some constructors might not be reachable

    lift' :: (v -> Maybe v0) -> TermVar v -> Maybe v0
    lift' _ (B _) = Nothing
    lift' f (F v) = f v

    ignoreNew _ (B _) = False
    ignoreNew f (F v) = f v

    addNew _ (B _) = True
    addNew f (F v) = f v

  return $ go Just (const False) t0

-- | Check whether a term @Def f es@ is finally stuck.
--   Currently, we give only a crude approximation.
isNeutral :: (IsTerm t, IsVar v) => Sig.Signature t -> Name -> [Elim (Term t) v] -> Bool
isNeutral sig f _ =
  case Sig.getDefinition sig f of
    Constant{}    -> True
    Constructor{} -> error $ "impossible.isNeutral: constructor " ++ show f
    Projection{}  -> error $ "impossible.isNeutral: projection " ++ show f
    Function{}    -> False
    -- TODO: more precise analysis
    -- We need to check whether a function is stuck on a variable
    -- (not meta variable), but the API does not help us...

-- | Returns True if it might be possible to get a data constructor out
-- of this term.
potentiallyMatchable :: (IsTerm t, IsVar v) => Term t v -> ClosedTC t Bool
potentiallyMatchable t = do
  sig <- getSignature
  case whnfView sig t of
    Lam body ->
      potentiallyMatchable (fromAbs body)
    Con dataCon args -> do
      if isRecordConstr sig dataCon
        then or <$> mapM potentiallyMatchable args
        else return True
    App (Def f) elims ->
      if isNeutral sig f elims
      then return False
      else return True
    _ ->
      return False

-- pruneMetaArguments
--   :: (IsVar v, IsTerm t)
--   => Type t v -> MetaVar -> [Elim (Term t) v]
--   -> TC t v (MetaVar, [Elim (Term t) v])
-- pruneMetaArguments = error "TODO pruneMetaArguments"

-- | 'Left' 'Just' if the pattern condition check is blocked on a some
-- 'MetaVar's.  The set is empty if the pattern condition is not
-- respected and no 'MetaVar' can change that.
--
-- 'Right' if the pattern condition is respected, with the distinct
-- variables.
checkPatternCondition
  :: (IsVar v, IsTerm t)
  => [Elim (Term t) v] -> TC t v (Either (Set.Set MetaVar) [v])
checkPatternCondition elims0 = do
  mbVsOrMvs <- go elims0
  return $ case mbVsOrMvs of
    Right vs -> if vs == nub vs then Right vs else Left Set.empty
    _        -> mbVsOrMvs
  where
    go
      :: (IsVar v, IsTerm t)
      => [Elim (Term t) v] -> TC t v (Either (Set.Set MetaVar) [v])
    go [] = return $ Right []
    go (elim : elims) = do
      elimOrMvs <- case elim of
        Apply t -> do
          -- TODO do we need to normalize here?
          blockedT <- whnfTC t
          return $ case blockedT of
            NotBlocked t' | App (Var v) [] <- view t' -> Right v
            MetaVarHead mv _                          -> Left $ Set.singleton mv
            BlockedOn mvs _ _                         -> Left mvs
            _                                         -> Left Set.empty
        _ ->
          return $ Left Set.empty
      elimsOrMvs <- go elims
      return $ case (elimOrMvs, elimsOrMvs) of
        (Left mvs1, Left mvs2) -> Left $ mvs1 <> mvs2
        (Left mvs, Right _)    -> Left mvs
        (Right _, Left mvs)    -> Left mvs
        (Right v, Right vs)    -> Right (v : vs)

-- | Creates a term in the same context as the original term but lambda
-- abstracted over the given variables.
lambdaAbstract :: (IsVar v, IsTerm t) => [v] -> Term t v -> Term t v
lambdaAbstract []       t = t
lambdaAbstract (v : vs) t = unview $ Lam $ abstract v $ lambdaAbstract vs t

data CloseTerm v0 a
    = Closed a
    | FlexibleOn (Set.Set MetaVar)
    | Rigid v0
    deriving (Functor)

instance Applicative (CloseTerm v0) where
    pure = Closed

    Closed f        <*> Closed x        = Closed (f x)
    Closed _        <*> FlexibleOn mvs  = FlexibleOn mvs
    Closed _        <*> Rigid v         = Rigid v
    FlexibleOn mvs  <*> Closed _        = FlexibleOn mvs
    FlexibleOn mvs1 <*> FlexibleOn mvs2 = FlexibleOn (mvs1 <> mvs2)
    FlexibleOn _    <*> Rigid v         = Rigid v
    Rigid v         <*> _               = Rigid v

-- TODO improve efficiency of this traversal, we shouldn't need all
-- those `fromAbs'.  Also in `rigidVars'.
closeTerm
    :: forall t v0.
       (IsVar v0, IsTerm t)
    => Term t v0 -> TC t v0 (CloseTerm v0 (Closed (Term t)))
closeTerm t0 = do
  sig <- getSignature
  let
    lift' :: (v -> Either v0 v') -> TermVar v -> Either v0 (TermVar v')
    lift' _ (B v) = Right $ B v
    lift' f (F v) = F <$> f v

    go :: (IsVar v, IsTerm t) => (v -> Either v0 v') -> Term t v
       -> CloseTerm v0 (t v')
    go strengthen t = unview <$>
      case whnfView sig t of
        Lam body ->
          (Lam . toAbs) <$> go (lift' strengthen) (fromAbs body)
        Pi dom cod ->
          (\dom' cod' -> Pi dom' (toAbs cod'))
            <$> go strengthen dom <*> go (lift' strengthen) (fromAbs cod)
        Equal type_ x y ->
          (\type' x' y' -> Equal type' x' y')
            <$> (go strengthen type_) <*> (go strengthen x) <*> (go strengthen y)
        Refl ->
          pure Refl
        Con dataCon args ->
          Con dataCon <$> sequenceA (map (go strengthen) args)
        Set ->
          pure Set
        App h elims ->
          let goElim (Apply t') = Apply <$> go strengthen t'
              goElim (Proj n f) = pure $ Proj n f

              resElims = sequenceA (map goElim elims)
          in case (h, resElims) of
               (Meta mv, FlexibleOn mvs)  ->
                 FlexibleOn $ Set.insert mv mvs
               (Meta mv, Rigid _) ->
                 FlexibleOn $ Set.singleton mv
               _ ->
                 App <$> traverse (either Rigid pure . strengthen) h
                     <*> resElims

  return $ go Left t0

-- Problem handling
-------------------

notStuck :: a -> StuckTC t v a
notStuck x = return $ NotStuck x

metaVarIfStuck
    :: (IsTerm t, IsVar v)
    => Type t v -> StuckTC t v (Term t v)
    -> TC t v (Term t v)
metaVarIfStuck type_ m = do
    stuck <- m
    case stuck of
      NotStuck t ->
        return t
      StuckOn pid -> do
        mv <- addMetaVarInCtx type_
        void $ bindProblem pid (MetaVarIfStuck mv type_ pid) $ checkEqual type_ mv
        return mv

elimStuckTC :: StuckTC t v a -> TC t v a -> TC t v a
elimStuckTC m ifStuck = do
    stuck <- m
    case stuck of
      NotStuck x   -> return x
      StuckOn _pid -> ifStuck

bindStuck
    :: (IsVar v, IsTerm t, Typeable a, Typeable b)
    => Stuck t v a -> (ProblemId t v a -> ProblemDescription t v)
    -> (a -> StuckTC t v b) -> StuckTC t v b
bindStuck (NotStuck x)  _    f = f x
bindStuck (StuckOn pid) desc f = StuckOn <$> bindProblem pid (desc pid) f

bindStuckTC
    :: (IsVar v, IsTerm t, Typeable a, Typeable b)
    => StuckTC t v a -> (ProblemId t v a -> ProblemDescription t v)
    -> (a -> StuckTC t v b) -> StuckTC t v b
bindStuckTC m desc f = do
    stuck <- m
    bindStuck stuck desc f

-- Checking definitions
------------------------------------------------------------------------

checkProgram
    :: ∀ t. (IsTerm t) => [A.Decl] -> IO (Either TCErr (TCState t))
checkProgram decls0 = do
    drawLine
    putStrLn "-- Checking declarations"
    drawLine
    runEitherT (goDecls initTCState decls0)
  where
    goDecls :: TCState t -> [A.Decl] -> EitherT TCErr IO (TCState t)
    goDecls ts [] = do
      lift $ report ts
      return ts
    goDecls ts (decl : decls) = do
      lift $ putStrLn $ render decl
      ((), ts') <- EitherT $ runTC ts $ checkDecl decl >> solveProblems
      goDecls ts' decls

    report :: TCState t -> IO ()
    report ts = do
      let tr  = tcReport ts
      let mvsTypes  = Sig.metaVarsTypes $ trSignature tr
      let mvsBodies = Sig.metaVarsBodies $ trSignature tr
      drawLine
      putStrLn $ "-- Solved MetaVars: " ++ show (Map.size mvsTypes)
      drawLine
      forM_ (Map.toList mvsTypes) $ \(mv, mvType) -> do
        forM_ (Map.lookup mv mvsBodies) $ \mvBody -> do
          putStrLn $ render $
            PP.pretty mv <+> ":" <+> PP.nest 2 (PP.pretty (view mvType))
          putStrLn $ render $
            PP.pretty mv <+> "=" <+> PP.nest 2 (PP.pretty (view mvBody))
      drawLine
      putStrLn "-- Unsolved MetaVars: "
      drawLine
      forM_ (Map.toList mvsTypes) $ \(mv, mvType) ->
        case Map.lookup mv mvsBodies of
          Nothing ->
            putStrLn $ render $
              PP.pretty mv <> PP.text " : " <> PP.nest 2 (PP.pretty (view mvType))
          Just _ ->
            return ()
      drawLine
      putStrLn $ "-- Solved problems: " ++ show (Set.size (trSolvedProblems tr))
      putStrLn $ "-- Unsolved problems: " ++ show (Map.size (trUnsolvedProblems tr))
      drawLine
      forM_ (Map.toList (trUnsolvedProblems tr)) $ \(pid, (probState, probDesc)) ->
        putStrLn $ render $
          PP.nest 2 (PP.pretty pid) $$
          PP.nest 4 (PP.pretty probState) $$
          PP.nest 4 probDesc

    drawLine =
      putStrLn "------------------------------------------------------------------------"

checkDecl :: (IsTerm t) => A.Decl -> ClosedTC t ()
checkDecl decl = atSrcLoc decl $ do
  case decl of
    A.TypeSig sig      -> checkTypeSig sig
    A.DataDef d xs cs  -> checkData d xs cs
    A.RecDef d xs c fs -> checkRec d xs c fs
    A.FunDef f ps b    -> checkClause f ps b

checkTypeSig :: (IsTerm t) => A.TypeSig -> ClosedTC t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- isType absType
    addConstant name Postulate type_

-- Data
-------

checkData
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> ClosedTC t ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon (Data []) tyConType
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        elimStuckTC (equalType endType set) $
          error $ "Type constructor does not return Set: " ++ show tyCon
        let appliedTyConType = ctxApp (def tyCon []) tyConPars'
        mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx.ClosedCtx (Type t) v
    -- ^ Ctx with the parameters of the tycon.
    -> Type t v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC t v ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
    atSrcLoc dataCon $ do
        dataConType <- isType synDataConType
        unrollPi dataConType $ \vs endType -> do
            let appliedTyConType' = fmap (Ctx.weaken vs) appliedTyConType
            elimStuckTC (equalType appliedTyConType' endType) $ do
              checkError $ TermsNotEqual appliedTyConType' endType
        addConstructor dataCon tyCon (Tel.idTel tyConPars dataConType)

-- Record
---------

checkRec
    :: (IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [A.TypeSig]
    -- ^ Fields of the record.
    -> ClosedTC t ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon (Record dataCon []) tyConType
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        void $ equalType endType set
        fieldsTel <- checkFields fields
        let appliedTyConType = ctxApp (def tyCon []) tyConPars'
        extendContext (A.name "_") appliedTyConType $ \self -> do
            addProjections
                tyCon tyConPars' self (map A.typeSigName fields) $
                (fmap F fieldsTel)
        Tel.unTel fieldsTel $ \fieldsCtx Tel.Proxy ->
            addConstructor dataCon tyCon $
            Tel.idTel tyConPars' $
            ctxPi fieldsCtx (fmap (Ctx.weaken fieldsCtx) appliedTyConType)

checkFields
    :: (IsVar v, IsTerm t) => [A.TypeSig] -> TC t v (Tel.ProxyTel (Type t) v)
checkFields = go Ctx.Empty
  where
    go :: (IsVar v, IsVar v', IsTerm t)
       => Ctx.Ctx v (Type t) v' -> [A.TypeSig] -> TC t v' (Tel.ProxyTel (Type t) v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType synFieldType
        extendContext field fieldType $ \_ ->
            go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx.ClosedCtx (Type t) v
    -- ^ A context with the parameters to the type constructor.
    -> TermVar v
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  We have
    -- a 'TermVar' here (and after) precisely because we're scoping over
    -- the self element after the tycon parameters above.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.ProxyTel (Type t) (TermVar v)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields.
    -> TC t (TermVar v) ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [0,1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
        ([], Tel.Empty Tel.Proxy) ->
            return ()
        ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
            let endType = pi (ctxApp (def tyCon []) tyConPars) (toAbs fieldType)
            addProjection field ix tyCon (Tel.idTel tyConPars endType)
            go fields' $
                Tel.instantiate fieldTypes' $ unview $ App (Var self) [Proj field ix]
        (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

-- Clause
---------

-- TODO what about pattern coverage?

checkClause :: (IsTerm t) => Name -> [A.Pattern] -> A.Expr -> ClosedTC t ()
checkClause fun synPats synClauseBody = do
    funType <- definitionType <$> getDefinition fun
    checkPatterns fun synPats funType $ \_ pats _ clauseType -> do
        clauseBody <- check synClauseBody clauseType
        ctx <- askContext
        addClause fun pats $ Scope $ fmap (toIntVar ctx) clauseBody
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx

checkPatterns
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> [A.Pattern]
    -> Type t v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (∀ v'. (IsVar v') => (v -> v') -> [Pattern] -> [Term t v'] -> Type t v' -> TC t v' a)
    -- ^ Handler taking a function to weaken an external variable,
    -- list of internal patterns, a list of terms produced by them, and
    -- the type of the clause body (scoped over the pattern variables).
    -> TC t v a
checkPatterns _ [] type_ ret =
    ret id [] [] type_
checkPatterns funName (synPat : synPats) type0 ret = atSrcLoc synPat $ do
  let err = ExpectedFunctionType type0 Nothing
  stuck <- matchPi_ type0 err $ \dom cod -> fmap NotStuck $ do
    checkPattern funName synPat dom $ \weaken_ pat patVar -> do
      let cod'  = fmap weaken_ cod
      let cod'' = instantiate cod' patVar
      checkPatterns funName synPats cod'' $ \weaken_' pats patsVars -> do
        let patVar' = fmap weaken_' patVar
        ret (weaken_' . weaken_) (pat : pats) (patVar' : patsVars)
  checkPatternStuck funName stuck

checkPattern
    :: (IsVar v, IsTerm t, Typeable a)
    => Name
    -> A.Pattern
    -> Type t v
    -- ^ Type of the matched thing.
    -> (∀ v'. (IsVar v') => (v -> v') -> Pattern -> Term t v' -> TC t v' a)
    -- ^ Handler taking a weakening function, the internal 'Pattern',
    -- and a 'Term' containing the term produced by it.
    -> TC t v a
checkPattern funName synPat type_ ret = case synPat of
    A.VarP name ->
      extendContext name type_ $ \v ->
      ret F VarP (var v)
    A.WildP _ ->
      extendContext (A.name "_") type_ $ \v ->
      ret F VarP (var v)
    A.ConP dataCon synPats -> do
      Constructor typeCon dataConType <- getDefinition dataCon
      typeConDef <- getDefinition typeCon
      case typeConDef of
        Constant (Data _)     _ -> return ()
        Constant (Record _ _) _ -> checkError $ PatternMatchOnRecord synPat typeCon
        _                       -> error $ "impossible.checkPattern" ++ render typeConDef
      let err = MismatchingPattern type_ synPat
      stuck <- matchTyCon typeCon type_ err $ \typeConArgs -> fmap NotStuck $ do
        let dataConTypeNoPars = Tel.substs (vacuous dataConType) typeConArgs
        checkPatterns funName synPats dataConTypeNoPars $ \weaken_ pats patsVars _ -> do
          let t = unview (Con dataCon patsVars)
          ret weaken_ (ConP dataCon pats) t
      checkPatternStuck funName stuck

-- TODO we can loosen this by postponing adding clauses.
checkPatternStuck :: (IsVar v, IsTerm t) => Name -> Stuck t v a -> TC t v a
checkPatternStuck funName stuck =
  case stuck of
    NotStuck x -> return x
    StuckOn _  -> checkError $ StuckTypeSignature funName

-- Utils
------------------------------------------------------------------------

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type to unroll
    -> [Name]
    -- ^ Names to give to each parameter
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t v' a)
    -- ^ Handler taking a context with accumulated domains of the pis
    -- and the final codomain.
    -> TC t v a
unrollPiWithNames type_ []             ret = ret Ctx.Empty type_
unrollPiWithNames type_ (name : names) ret = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain ->
      extendContext name domain $ \_v ->
      unrollPiWithNames (fromAbs codomain) names $ \ctxVs endType ->
      ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      checkError $ ExpectedFunctionType type_ Nothing

unrollPi
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type to unroll
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t v' a)
    -- ^ Handler taking a weakening function, the list of domains
    -- of the unrolled pis, the final codomain.
    -> TC t v a
unrollPi type_ ret = do
  typeView <- whnfViewTC type_
  case typeView of
    Pi domain codomain -> do
      let codomain' = fromAbs codomain
      let name      = getName_ codomain'
      extendContext name domain $ \_v ->
        unrollPi codomain' $ \ctxVs endType ->
        ret (Ctx.singleton name domain Ctx.++ ctxVs) endType
    _ ->
      ret Ctx.Empty type_

-- Definition utils
-------------------

addConstant
    :: (IsVar v, IsTerm t)
    => Name -> ConstantKind -> Closed (Type t) -> TC t v ()
addConstant x k a = addDefinition x (Constant k a)

addConstructor
    :: (IsVar v, IsTerm t)
    => Name -> Name -> Tel.ClosedIdTel (Type t) -> TC t v ()
addConstructor c d tel = addDefinition c (Constructor d tel)

addProjection
    :: (IsVar v, IsTerm t)
    => Name -> Field -> Name -> Tel.ClosedIdTel (Type t) -> TC t v ()
addProjection f n r tel = addDefinition f (Projection n r tel)

addClause
    :: (IsVar v, IsTerm t)
    => Name -> [Pattern] -> ClauseBody (Term t) Void -> TC t v ()
addClause f ps v = do
  def' <- getDefinition f
  let ext (Constant Postulate a) = Function a [c]
      ext (Function a cs)        = Function a (cs ++ [c])
      ext (Constant k _)         = error $ "Monad.addClause " ++ render k
      ext Constructor{}          = error $ "Monad.addClause constructor"
      ext Projection{}           = error $ "Monad.addClause projection"
  addDefinition f (ext def')
  where
    c = Clause ps v

definitionType :: (IsTerm t) => Closed (Definition t) -> Closed (Type t)
definitionType (Constant _ type_)   = type_
definitionType (Constructor _ tel)  = telPi tel
definitionType (Projection _ _ tel) = telPi tel
definitionType (Function type_ _)   = type_

isRecordType :: (IsTerm t) => Sig.Signature t -> Name -> Bool
isRecordType sig tyCon =
  case Sig.getDefinition sig tyCon of
    Constant (Record _ _) _ -> True
    _                       -> False

isRecordConstr :: (IsTerm t) => Sig.Signature t -> Name -> Bool
isRecordConstr sig dataCon =
  case Sig.getDefinition sig dataCon of
    Constructor tyCon _ -> isRecordType sig tyCon
    _                   -> False

-- Whnf'ing and view'ing
------------------------

whnfTC :: (IsTerm t) => t v -> TC t v' (Blocked t v)
whnfTC t = do
  sig <- getSignature
  return $ whnf sig t

whnfViewTC :: (IsTerm t) => t v -> TC t v' (TermView t v)
whnfViewTC t = view . ignoreBlocking <$> whnfTC t

whnfView :: (IsTerm t) => Sig.Signature t -> t v -> TermView t v
whnfView sig = view . ignoreBlocking . whnf sig

-- Matching terms
-----------------

-- TODO remove duplication

matchTyCon
  :: (IsVar v, IsTerm t, Typeable a)
  => Name
  -> Type t v
  -> CheckError t v             -- ^ Error
  -> ([Term t v] -> StuckTC t v a)
  -> StuckTC t v a
matchTyCon tyCon t err handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _
      | App (Def tyCon') tyConArgs0 <- view t'
      , tyCon == tyCon', Just tyConArgs <- mapM isApply tyConArgs0 -> do
        handler tyConArgs
    MetaVarHead mv _ -> do
      liftClosed $ do
        mvType <- getTypeOfMetaVar mv
        mvT <- unrollPi mvType $ \ctxMvArgs _ -> do
          Constant _ tyConType <- getDefinition tyCon
          tyConParsTel <- unrollPi (vacuous tyConType) $ \ctx ->
                          return . Tel.idTel ctx
          tyConPars <- createTyConParsMvs tyConParsTel
          return $ ctxLam ctxMvArgs $ def tyCon $ map Apply tyConPars
        instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchTyCon tyCon t' err handler
    BlockedOn mvs _ _ -> do
      fmap StuckOn $ newProblem mvs (MatchTyCon tyCon t') $ \_ -> do
        matchTyCon tyCon t' err handler
    _ -> do
      NotStuck <$> checkError err

matchPi
  :: (IsVar v, IsTerm t, Typeable a)
  => Name                       -- ^ Name for the bound var in the codomain.
  -> Type t v
  -> CheckError t v             -- ^ Error
  -> (Type t v -> Abs (Type t) v -> StuckTC t v a)
  -> StuckTC t v a
matchPi name t err handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _ | Pi dom cod <- view t' -> do
      handler dom cod
    MetaVarHead mv _ -> do
      liftClosed $ do
        mvType <- getTypeOfMetaVar mv
        mvT <- unrollPi mvType $ \ctxMvArgs _ -> do
          dom <- addMetaVarInCtx set
          cod <- extendContext name dom $ \_ -> addMetaVarInCtx set
          return $ ctxLam ctxMvArgs $ pi dom $ toAbs cod
        instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchPi name t' err handler
    BlockedOn mvs _ _ -> do
      fmap StuckOn $ newProblem mvs (MatchPi t') $ \_ -> do
        matchPi name t' err handler
    _ -> do
      NotStuck <$> checkError err

matchPi_
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> CheckError t v             -- ^ Error
  -> (Type t v -> Abs (Type t) v -> StuckTC t v a)
  -> StuckTC t v a
matchPi_ = matchPi "_"

matchEqual
  :: (IsVar v, IsTerm t, Typeable a)
  => Type t v
  -> CheckError t v             -- ^ Error
  -> (Type t v -> Term t v -> Term t v -> StuckTC t v a)
  -> StuckTC t v a
matchEqual t err handler = do
  blockedT <- whnfTC t
  let t' = ignoreBlocking blockedT
  case blockedT of
    NotBlocked _ | Equal type_ t1 t2 <- view t' -> do
      handler type_ t1 t2
    MetaVarHead mv _ -> do
      liftClosed $ do
        mvType <- getTypeOfMetaVar mv
        mvT <- unrollPi mvType $ \ctxMvArgs _ -> do
          type_ <- addMetaVarInCtx set
          t1 <- addMetaVarInCtx type_
          t2 <- addMetaVarInCtx type_
          return $ ctxLam ctxMvArgs $ equal type_ t1 t2
        instantiateMetaVar mv mvT
      -- TODO Dangerous recursion, relying on correct instantiation.
      -- Maybe remove and do it explicitly?
      matchEqual t' err handler
    BlockedOn mvs _ _ ->
      fmap StuckOn $ newProblem mvs (MatchEqual t') $ \_ -> do
        matchEqual t' err handler
    _ -> do
      NotStuck <$> checkError err

-- Problems shortcuts
---------------------

newProblemCheckEqual
    :: (IsTerm t, IsVar v, Typeable v, Typeable t)
    => Set.Set MetaVar -> Type t v -> Term t v -> Term t v
    -> TC t v (ProblemId t v ())
newProblemCheckEqual mvs type_ x y = do
    newProblem mvs (CheckEqual type_ x y) $ \_ -> checkEqual type_ x y

waitOnProblemCheckEqual
    :: (IsTerm t, IsVar v, Typeable a, Typeable v, Typeable t)
    => ProblemId t v' a -> Type t v -> Term t v -> Term t v -> TC t v (ProblemId t v())
waitOnProblemCheckEqual pid type_ x y = do
    waitOnProblem pid (CheckEqual type_ x y) $ checkEqual type_ x y

-- Errors
------------------------------------------------------------------------

data CheckError t v
    = ConstructorTypeError A.Expr (Type t v)
    | LambdaTypeError A.Expr (Type t v)
    | NotEqualityType (Type t v)
    | ExpectedFunctionType (Type t v) (Maybe A.Expr)
    | CannotInferTypeOf A.Expr
    | TermsNotEqual (Term t v) (Term t v)
    | SpineNotEqual (Type t v) [Elim t v] [Elim t v]
    | ExpectingRecordType (Type t v)
    | FreeVariableInEquatedTerm MetaVar [Elim t v] (Term t v) v
    | PatternMatchOnRecord A.Pattern
                           Name -- Record type constructor
    | MismatchingPattern (Type t v) A.Pattern
    | OccursCheckFailed MetaVar (Term t v)
    | NameNotInScope Name
    | StuckTypeSignature Name

checkError :: (IsVar v, IsTerm t) => CheckError t v -> TC t v a
checkError err = do
    sig <- getSignature
    typeError $ renderError sig err
  where
    renderError sig (ConstructorTypeError synT type_) =
      "Constructor type error " ++ render synT ++ " : " ++ renderTerm sig type_
    renderError sig (NotEqualityType type_) =
      "Expecting an equality type: " ++ renderTerm sig type_
    renderError sig (LambdaTypeError synT type_) =
      "Lambda type error\n" ++ render synT ++ "\n  :\n" ++ renderTerm sig type_
    renderError sig (ExpectedFunctionType type_ mbArg) =
      "Expected function type " ++ renderTerm sig type_ ++
      (case mbArg of
         Nothing  -> ""
         Just arg -> "\nIn application of " ++ render arg)
    renderError _ (CannotInferTypeOf synT) =
      "Cannot infer type of " ++ render synT
    renderError sig (TermsNotEqual t1 t2) =
      renderTerm sig t1 ++ "\n  !=\n" ++ renderTerm sig t2
    renderError sig (SpineNotEqual type_ es1 es2) =
      render es1 ++ "\n  !=\n" ++ render es2 ++ "\n  :\n" ++ renderTerm sig type_
    renderError sig (ExpectingRecordType type_) =
      "Expecting record type: " ++ renderTerm sig type_
    renderError sig (FreeVariableInEquatedTerm mv els rhs v) =
      "Free variable `" ++ renderVar v ++ "' in term equated to metavariable application:\n" ++
      renderTerm sig (metaVar mv els) ++ "\n" ++
      "  =\n" ++
      renderTerm sig rhs
    renderError _ (PatternMatchOnRecord synPat tyCon) =
      "Cannot have pattern " ++ render synPat ++ " for record type " ++ render tyCon
    renderError sig (MismatchingPattern type_ synPat) =
      render synPat ++ " does not match an element of type " ++ renderTerm sig type_
    renderError sig (OccursCheckFailed mv t) =
      "Attempt at recursive instantiation: " ++ render mv ++ " := " ++ renderTerm sig t
    renderError _ (NameNotInScope name) =
      "Name not in scope: " ++ render name
    renderError _ (StuckTypeSignature name) =
      "Got stuck on the type signature when checking clauses for function " ++ render name

    renderVar = render . varName
    renderTerm sig = render . prettyTerm sig

prettyTerm :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> PP.Doc
prettyTerm sig = PP.pretty . view . instantiateMetaVars sig

instantiateMetaVars :: (IsVar v, IsTerm t) => Sig.Signature t -> t v -> t v
instantiateMetaVars sig t = unview $
  case view t of
    Lam abs ->
      Lam (goAbs abs)
    Pi dom cod ->
      Pi (go dom) (goAbs cod)
    Equal type_ x y ->
      Equal (go type_) (go x) (go y)
    Refl ->
      Refl
    Con dataCon ts ->
      Con dataCon $ map go ts
    Set ->
      Set
    App (Meta mv) els | Just t' <- Sig.getMetaVarBody sig mv ->
      view $ instantiateMetaVars sig $ eliminate (vacuousM t') els
    App h els ->
      App h $ map goElim els
  where
    go = instantiateMetaVars sig

    goAbs = toAbs . instantiateMetaVars sig . fromAbs

    goElim (Proj n field) = Proj n field
    goElim (Apply t')     = Apply (go t')

-- Non-monadic stuff
------------------------------------------------------------------------

isApply :: Elim (Term t) v -> Maybe (Term t v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

-- Telescope & context utils
------------------

telPi :: (IsVar v, IsTerm t) => Tel.IdTel (Type t) v -> Type t v
telPi tel = Tel.unTel tel $ \ctx endType -> ctxPi ctx (Tel.unId endType)

-- | Collects all the variables in the 'Ctx.Ctx'.
ctxVars :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
ctxVars = go
  where
    go :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
    go Ctx.Empty                = []
    go (Ctx.Snoc ctx (name, _)) = boundTermVar name : map F (go ctx)

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
ctxApp :: IsTerm t => Term t v -> Ctx.Ctx v0 (Type t) v -> Term t v
ctxApp t ctx0 = eliminate t $ map (Apply . var) $ reverse $ ctxVars ctx0

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Type t v -> Type t v0
ctxPi Ctx.Empty                  t = t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx $ pi type_ (toAbs t)

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx.Ctx'.
ctxLam :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Term t v -> Term t v0
ctxLam Ctx.Empty        t = t
ctxLam (Ctx.Snoc ctx _) t = ctxLam ctx $ lam $ toAbs t

-- Types of problems
------------------------------------------------------------------------

data ProblemDescription t v
    = CheckEqual (Type t v) (Term t v) (Term t v)
    | WaitForInfer A.Expr (Type t v)
    | forall a. EscapingScope (ProblemId t v a)
    | MetaVarIfStuck (Term t v) (Type t v) (ProblemId t v (Term t v))
    | forall a. WaitingOn (ProblemId t v a)
    | CheckSpine (Term t v) [A.Elim] (Type t v)
    | EqualSpine (Term t v) [Elim t v] [Elim t v] (Type t v)
    | MatchTyCon Name (Type t v)
    | MatchPi (Type t v)
    | MatchEqual (Type t v)

instance (IsVar v, IsTerm t) => PP.Pretty (ProblemDescription t v)  where
    pretty desc = case desc of
      CheckEqual type_ x y ->
        prettyView x $$ PP.nest 2 "=" $$ prettyView y $$
        PP.nest 2 ":" $$
        prettyView type_
      WaitForInfer synT type_ ->
        "Waiting for inference of" $$ PP.nest 2 (
          PP.pretty synT $$ PP.nest 2 ":" $$ prettyView type_)
      EscapingScope pid ->
        "Escaping scope" <+> PP.text (show pid)
      MetaVarIfStuck mvT type_ pid | App (Meta mv) _ <- view mvT ->
        "Waiting to equate placeholder" <+> PP.pretty mv <+> "of type" $$
        PP.nest 2 (prettyView type_) $$
        "to result of problem" <+> PP.text (show pid)
      MetaVarIfStuck mvT _ _ ->
        error $ "PP.Pretty ProblemDescription: got non-meta term: " ++ renderView mvT
      WaitingOn pid ->
        "Waiting on" <+> PP.text (show pid)
      CheckSpine t elims type_ ->
        "Checking spine" $$ PP.nest 2 (
          PP.prettyApp 0 (prettyView t) elims $$ PP.nest 2 ":" $$ prettyView type_)
      EqualSpine h elims1 elims2 type_ ->
        "Equating spine" $$ PP.nest 2 (prettyView h) $$ PP.nest 2 (
          PP.pretty elims1 $$ PP.nest 2 "=" $$ PP.pretty elims2 $$
          PP.nest 2 ":" $$
          prettyView type_)
      MatchTyCon name type_ ->
        ("Matching tycon" <+> PP.pretty name <+> "with type") $$ prettyView type_
      MatchPi type_ ->
        "Matching pi type" $$ prettyView type_
      MatchEqual type_ ->
        "Matching equal" $$ prettyView type_

-- Constants
------------------------------------------------------------------------

-- (A : Set) ->
-- (x : A) ->
-- (y : A) ->
-- (P : (x : A) -> (y : A) -> (eq : _==_ A x y) -> Set) ->
-- (p : (x : A) -> P x x refl) ->
-- (eq : _==_ A x y) ->
-- P x y eq
typeOfJ :: forall t. (IsTerm t) => Closed (Type t)
typeOfJ =  fmap close $
    ("A", set) -->
    ("x", var "A") -->
    ("y", var "A") -->
    ("P", ("x", var "A") --> ("y", var "A") -->
          ("eq", equal (var "A") (var "x") (var "y")) -->
          set
    ) -->
    ("p", ("x", var "A") --> app (Var "P") (map Apply [var "x", var "x", refl])) -->
    ("eq", equal (var "A") (var "x") (var "y")) -->
    app (Var "P") (map Apply [var "x", var "y", refl])
  where
    close :: Name -> Void
    close v = error $ "impossible.typeOfJ: Free variable " ++ render v

    infixr 9 -->
    (-->) :: (Name, t Name) -> t Name -> t Name
    (x, type_) --> t = pi type_ $ abstract x t
