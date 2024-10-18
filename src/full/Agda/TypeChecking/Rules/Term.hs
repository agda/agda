{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Term where

import Prelude hiding ( null )

import Control.Monad.Except ( MonadError(..) )

import Data.Maybe
import Data.Either (partitionEithers, lefts)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Generate (disambiguateRecordFields)

import Agda.Syntax.Abstract (Binder, TypedBindingInfo (tbTacticAttr))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Concrete.Pretty () -- only Pretty instances
import Agda.Syntax.Concrete (FieldAssignment'(..), nameFieldA, TacticAttribute'(..))
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Scope.Base ( ThingsInScope, AbstractName
                              , emptyScopeInfo
                              , exportedNamesInScope)
import Agda.Syntax.Scope.Monad (getNamedScope)

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Generalize
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.IApplyConfluence
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Quote
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rules.LHS
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.SizedTypes.Solve
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Unquote
import Agda.TypeChecking.Warnings

import {-# SOURCE #-} Agda.TypeChecking.Empty ( ensureEmptyType )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Def (checkFunDef', useTerPragma)
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl (checkSectionApplication)
import {-# SOURCE #-} Agda.TypeChecking.Rules.Application

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1  ( List1, pattern (:|) )
import Agda.Utils.List2  ( pattern List2 )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Check that an expression is a type.
isType :: A.Expr -> Sort -> TCM Type
isType = isType' CmpLeq

-- | Check that an expression is a type.
--   * If @c == CmpEq@, the given sort must be the minimal sort.
--   * If @c == CmpLeq@, the given sort may be any bigger sort.
isType' :: Comparison -> A.Expr -> Sort -> TCM Type
isType' c e s =
    traceCall (IsTypeCall c e s) $ do
    v <- checkExpr' c e (sort s)
    return $ El s v

-- | Check that an expression is a type and infer its (minimal) sort.
isType_ :: A.Expr -> TCM Type
isType_ e = traceCall (IsType_ e) $ do
  reportResult "tc.term.istype" 15 (\a -> vcat
    [ "isType_" <?> prettyTCM e
    , nest 2 $ "returns" <?> prettyTCM a
    ]) $ do
  let fallback = isType' CmpEq e =<< do workOnTypes $ newSortMeta
  SortKit{..} <- sortKit
  case unScope e of
    A.Fun i (Arg info t) b -> do
      a <- setArgInfo info . defaultDom <$> checkPiDomain (info :| []) t
      b <- isType_ b
      s <- inferFunSort a (getSort b)
      let t' = El s $ Pi a $ NoAbs underscore b
      checkTelePiSort t'
      --noFunctionsIntoSize t'
      return t'
    A.Pi _ tel e -> do
      (t0, t') <- checkPiTelescope (List1.toList tel) $ \ tel -> do
        t0  <- instantiateFull =<< isType_ e
        tel <- instantiateFull tel
        return (t0, telePi tel t0)
      checkTelePiSort t'
      --noFunctionsIntoSize t'
      return t'

    A.Generalized s e -> do
      (_, t') <- generalizeType (Set1.toSet s) $ isType_ e
      --noFunctionsIntoSize t'
      return t'

    -- Prop/(S)Set(ω)ᵢ
    A.Def' x suffix
      | Just (sz, u) <- isNameOfUniv x
      , let n = suffixToLevel suffix
      -> do
        univChecks u
        return . sort $ case sz of
          USmall -> Univ u $ ClosedLevel n
          ULarge -> Inf u n

    -- Prop/(S)et ℓ
    A.App i s arg
      | visible arg,
        A.Def x <- unScope s,
        Just (USmall, u) <- isNameOfUniv x -> do
      univChecks u
      unlessM hasUniversePolymorphism $ typeError NeedOptionUniversePolymorphism
      -- allow ShapeIrrelevant variables when checking level
      --   Set : (ShapeIrrelevant) Level -> Set\omega
      applyRelevanceToContext shapeIrrelevant $
        sort . Univ u <$> checkLevel arg

    -- Issue #707: Check an existing interaction point
    A.QuestionMark minfo ii -> caseMaybeM (lookupInteractionMeta ii) fallback $ \ x -> do
      -- -- | Just x <- A.metaNumber minfo -> do
      reportSDoc "tc.ip" 20 $ fsep
        [ "Rechecking meta "
        , prettyTCM x
        , text $ " for interaction point " ++ show ii
        ]
      mv <- lookupLocalMeta x
      let s0 = jMetaType . mvJudgement $ mv
      -- Andreas, 2016-10-14, issue #2257
      -- The meta was created in a context of length @n@.
      let n  = length . envContext . clEnv . miClosRange . mvInfo $ mv
      (vs, rest) <- splitAt n <$> getContextArgs
      reportSDoc "tc.ip" 20 $ vcat
        [ "  s0   = " <+> prettyTCM s0
        , "  vs   = " <+> prettyTCM vs
        , "  rest = " <+> prettyTCM rest
        ]
      -- We assume the meta variable use here is in an extension of the original context.
      -- If not we revert to the old buggy behavior of #707 (see test/Succeed/Issue2257b).
      if (length vs /= n) then fallback else do
      s1  <- reduce =<< piApplyM s0 vs
      reportSDoc "tc.ip" 20 $ vcat
        [ "  s1   = " <+> prettyTCM s1
        ]
      reportSDoc "tc.ip" 70 $ vcat
        [ "  s1   = " <+> text (show s1)
        ]
      case unEl s1 of
        Sort s -> return $ El s $ MetaV x $ map Apply vs
        _ -> __IMPOSSIBLE__

    _ -> fallback

checkLevel :: NamedArg A.Expr -> TCM Level
checkLevel arg = do
  lvl <- levelType
  levelView =<< checkNamedArg arg lvl

-- | Ensure that a (freshly created) function type does not inhabit 'SizeUniv'.
--   Precondition:  When @noFunctionsIntoSize t tBlame@ is called,
--   we are in the context of @tBlame@ in order to print it correctly.
--   Not being in context of @t@ should not matter, as we are only
--   checking whether its sort reduces to 'SizeUniv'.
--
--   Currently UNUSED since SizeUniv is turned off (as of 2016).
{-
noFunctionsIntoSize :: Type -> Type -> TCM ()
noFunctionsIntoSize t tBlame = do
  reportSDoc "tc.fun" 20 $ do
    let El s (Pi dom b) = tBlame
    sep [ "created function type " <+> prettyTCM tBlame
        , "with pts rule (" <+> prettyTCM (getSort dom) <+>
                        "," <+> underAbstraction_ b (prettyTCM . getSort) <+>
                        "," <+> prettyTCM s <+> ")"
        ]
  s <- reduce $ getSort t
  when (s == SizeUniv) $ do
    -- Andreas, 2015-02-14
    -- We have constructed a function type in SizeUniv
    -- which is illegal to prevent issue 1428.
    typeError $ FunctionTypeInSizeUniv $ unEl tBlame
-}

-- | Check that an expression is a type which is equal to a given type.
isTypeEqualTo :: A.Expr -> Type -> TCM Type
isTypeEqualTo e0 t = scopedExpr e0 >>= \case
  A.ScopedExpr{} -> __IMPOSSIBLE__
  A.Underscore i | isNothing (A.metaNumber i) -> return t
  e -> workOnTypes $ do
    t' <- isType e (getSort t)
    t' <$ leqType t t'

leqType_ :: Type -> Type -> TCM ()
leqType_ t t' = workOnTypes $ leqType t t'

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

checkGeneralizeTelescope ::
     Maybe ModuleName
       -- ^ The module the telescope belongs to (if any).
  -> A.GeneralizeTelescope
       -- ^ Telescope to check and add to the context for the continuation.
  -> ([Maybe Name] -> Telescope -> TCM a)
       -- ^ Continuation living in the extended context.
  -> TCM a
checkGeneralizeTelescope mm (A.GeneralizeTel vars tel) =
    tr (generalizeTelescope vars (checkTelescope tel) . curry) . uncurry
  where
    tr = applyUnless (null tel) $ applyWhenJust mm $ \ m ->
      traceCallCPS $ CheckModuleParameters m tel

-- | Type check a (module) telescope.
--   Binds the variables defined by the telescope.
checkTelescope :: A.Telescope -> (Telescope -> TCM a) -> TCM a
checkTelescope = checkTelescope' LamNotPi

-- | Type check the telescope of a dependent function type.
--   Binds the resurrected variables defined by the telescope.
--   The returned telescope is unmodified (not resurrected).
checkPiTelescope :: A.Telescope -> (Telescope -> TCM a) -> TCM a
checkPiTelescope = checkTelescope' PiNotLam

-- | Flag to control resurrection on domains.
data LamOrPi
  = LamNotPi -- ^ We are checking a module telescope.
             --   We pass into the type world to check the domain type.
             --   This resurrects the whole context.
  | PiNotLam -- ^ We are checking a telescope in a Pi-type.
             --   We stay in the term world, but add resurrected
             --   domains to the context to check the remaining
             --   domains and codomain of the Pi-type.
  deriving (Eq, Show)

-- | Type check a telescope. Binds the variables defined by the telescope.
checkTelescope' :: LamOrPi -> A.Telescope -> (Telescope -> TCM a) -> TCM a
checkTelescope' lamOrPi []        ret = ret EmptyTel
checkTelescope' lamOrPi (b : tel) ret =
    checkTypedBindings lamOrPi b $ \tel1 ->
    checkTelescope' lamOrPi tel  $ \tel2 ->
        ret $ abstract tel1 tel2

-- | Check the domain of a function type.
--   Used in @checkTypedBindings@ and to typecheck @A.Fun@ cases.
checkDomain :: (LensLock a, LensModality a) => LamOrPi -> List1 a -> A.Expr -> TCM Type
checkDomain lamOrPi xs e = do
    -- Get cohesion and quantity of arguments, which should all be equal because
    -- they come from the same annotated Π-type.
    let (c :| cs) = fmap (getCohesion . getModality) xs
    unless (all (c ==) cs) $ __IMPOSSIBLE__

    let (q :| qs) = fmap (getQuantity . getModality) xs
    unless (all (q ==) qs) $ __IMPOSSIBLE__

    t <- applyQuantityToJudgement q $
         applyCohesionToContext c $
         applyPolarityToContext negativePolarity $
         modEnv lamOrPi $ isType_ e
    -- Andrea TODO: also make sure that LockUniv implies IsLock
    when (any (\x -> case getLock x of { IsLock{} -> True ; _ -> False }) xs) $ do
         -- Solves issue #5033
        unlessM (isJust <$> getName' builtinLockUniv) $ do
          typeError $ NoBindingForPrimitive builtinLockUniv

        equalSort (getSort t) LockUniv

    return t
  where
        -- if we are checking a typed lambda, we resurrect before we check the
        -- types, but do not modify the new context entries
        -- otherwise, if we are checking a pi, we do not resurrect, but
        -- modify the new context entries
        modEnv LamNotPi = workOnTypes
        modEnv _        = id

checkPiDomain :: (LensLock a, LensModality a) => List1 a -> A.Expr -> TCM Type
checkPiDomain = checkDomain PiNotLam

-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
--
--   Parametrized by a flag whether we check a typed lambda or a Pi. This flag
--   is needed for irrelevance.

checkTypedBindings :: LamOrPi -> A.TypedBinding -> (Telescope -> TCM a) -> TCM a
checkTypedBindings lamOrPi (A.TBind r tac xps e) ret = do
    let xs = fmap (updateNamedArg $ A.unBind . A.binderName) xps
    tac <- traverse (checkTacticAttribute lamOrPi) $ theTacticAttribute $ tbTacticAttr tac
    whenJust tac $ \ t -> reportSDoc "tc.term.tactic" 30 $ "Checked tactic attribute:" <?> prettyTCM t
    -- Andreas, 2011-04-26 irrelevant function arguments may appear
    -- non-strictly in the codomain type
    -- 2011-10-04 if flag --experimental-irrelevance is set
    experimental <- optExperimentalIrrelevance <$> pragmaOptions

    t <- checkDomain lamOrPi xps e

    -- Jesper, 2019-02-12, Issue #3534: warn if the type of an
    -- instance argument does not have the right shape
    List1.unlessNull (List1.filter isInstance xps) $ \ ixs -> do
      (tel, _, target) <- getOutputTypeName t
      case target of
        OutputTypeName{} -> return ()
        OutputTypeVar{}  -> return ()
        OutputTypeNameNotYetKnown{} -> return ()
        OutputTypeVisiblePi{} -> setCurrentRange e $
          warning . InstanceArgWithExplicitArg =<< prettyTCM (A.mkTBind r ixs e)
        NoOutputTypeName -> setCurrentRange e $
          warning . InstanceNoOutputTypeName =<< prettyTCM (A.mkTBind r ixs e)

    let setTac tac EmptyTel            = EmptyTel
        setTac tac (ExtendTel dom tel) = ExtendTel dom{ domTactic = tac } $ setTac (raise 1 tac) <$> tel
        xs' = fmap (modMod lamOrPi experimental) xs
    let tel = setTac tac $ namedBindsToTel1 xs t

    addContext (xs', t) $ addTypedPatterns xps (ret tel)

    where
        -- if we are checking a typed lambda, we resurrect before we check the
        -- types, but do not modify the new context entries
        -- otherwise, if we are checking a pi, we do not resurrect, but
        -- modify the new context entries
        modEnv LamNotPi = workOnTypes
        modEnv _        = id
        modMod PiNotLam xp = inverseApplyPolarity (withStandardLock UnusedPolarity)
                             . applyWhen xp (mapRelevance irrelevantToShapeIrrelevant)
        modMod _        _  = id

checkTypedBindings lamOrPi (A.TLet _ lbs) ret = do
    checkLetBindings lbs (ret EmptyTel)

-- | After a typed binding has been checked, add the patterns it binds
addTypedPatterns :: List1 (NamedArg A.Binder) -> TCM a -> TCM a
addTypedPatterns xps ret = do
  let ps  = List1.mapMaybe (A.extractPattern . namedArg) xps
  let lbs = map letBinding ps
  checkLetBindings lbs ret
  where
    letBinding :: (A.Pattern, A.BindName) -> A.LetBinding
    letBinding (p, n) = A.LetPatBind (A.LetRange r) p (A.Var $ A.unBind n)
      where r = fuseRange p n

-- | Check a tactic attribute. Should have type Term → TC ⊤.
checkTacticAttribute :: LamOrPi -> Ranged A.Expr -> TCM Term
checkTacticAttribute LamNotPi (Ranged r e) = setCurrentRange r $
  typeError $ TacticAttributeNotAllowed
checkTacticAttribute PiNotLam (Ranged r e) = do
  expectedType <- el primAgdaTerm --> el (primAgdaTCM <#> primLevelZero <@> primUnit)
  checkExpr e expectedType

checkPath :: NamedArg Binder -> A.Type -> A.Expr -> Type -> TCM Term
checkPath xp typ body ty = do
 reportSDoc "tc.term.lambda" 30 $ hsep [ "checking path lambda", prettyA xp ]
 case (A.extractPattern $ namedArg xp) of
  Just{}  -> setCurrentRange xp $ typeError PatternInPathLambda
  Nothing -> do
    let x    = updateNamedArg (A.unBind . A.binderName) xp
        info = getArgInfo x
    PathType s path level typ lhs rhs <- pathView ty
    interval <- primIntervalType
    v <- addContext ([x], interval) $
           checkExpr body (El (raise 1 s) (raise 1 (unArg typ) `apply` [argN $ var 0]))
    iZero <- primIZero
    iOne  <- primIOne
    let lhs' = subst 0 iZero v
        rhs' = subst 0 iOne  v
    let t = Lam info $ Abs (namedArgName x) v
    let btyp i = El s (unArg typ `apply` [argN i])
    locallyTC eRange (const noRange) $ blockTerm ty $ setCurrentRange body $ do
      equalTerm (btyp iZero) lhs' (unArg lhs)
      equalTerm (btyp iOne) rhs' (unArg rhs)
      return t

---------------------------------------------------------------------------
-- * Lambda abstractions
---------------------------------------------------------------------------

-- | Type check a lambda expression.
--   "checkLambda bs e ty"  means  (\ bs -> e) : ty
checkLambda :: Comparison -> A.TypedBinding -> A.Expr -> Type -> TCM Term
checkLambda cmp (A.TLet _ lbs) body target =
  checkLetBindings lbs (checkExpr body target)
checkLambda cmp b@(A.TBind r tac xps0 typ) body target = do
  reportSDoc "tc.term.lambda" 30 $ vcat
    [ "checkLambda before insertion xs =" <+> prettyA xps0
    ]
  -- Andreas, 2020-03-25, issue #4481: since we have named lambdas now,
  -- we need to insert skipped hidden arguments.
  xps <- insertImplicitBindersT1 xps0 target
  checkLambda' cmp r tac xps typ body target

checkLambda' ::
     Comparison                -- ^ @cmp@
  -> Range                     -- ^ Range @r@ of the typed binding
  -> A.TypedBindingInfo        -- ^ @tac@ tactic/finiteness attribute of the typed binding
  -> List1 (NamedArg Binder)   -- ^ @xps@ variables/patterns of the typed binding
  -> A.Type                    -- ^ @typ@ Type of the typed binding
  -> A.Expr                    -- ^ @body@
  -> Type                      -- ^ @target@
  -> TCM Term
checkLambda' cmp r tac xps typ body target = do
  reportSDoc "tc.term.lambda" 30 $ vcat
    [ "checkLambda xs =" <+> prettyA xps
    , "possiblePath   =" <+> prettyTCM possiblePath
    , "numbinds       =" <+> prettyTCM numbinds
    , "typ            =" <+> prettyA   (unScope typ)
    , "tactic         =" <+> prettyA (tbTacticAttr tac)
    ]
  reportSDoc "tc.term.lambda" 60 $ vcat
    [ "info           =" <+> (text . show) info
    ]

  -- Consume @tac@:
  case tac of
    _ | null tac -> pure ()
    A.TypedBindingInfo{ tbTacticAttr = TacticAttribute (Just tactic) } -> do
      -- Andreas, 2024-02-22, issue #6783
      -- Error out if user supplied a tactic (rather than dropping it silently).
      _tactic <- checkTacticAttribute LamNotPi tactic
      -- We should not survive this check...
      __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

  TelV tel btyp <- telViewUpTo numbinds target
  if numbinds == 1 && not (null tel) then useTargetType tel btyp
  else if possiblePath then trySeeingIfPath
  else dontUseTargetType

  where
    b = A.TBind r tac xps typ
    xs = fmap (updateNamedArg (A.unBind . A.binderName)) xps
    numbinds = length xps
    possiblePath = numbinds == 1 && isUnderscore (unScope typ)
                   && isRelevant info && visible info
    info = getArgInfo $ List1.head xs

    trySeeingIfPath = do
      reportSLn "tc.term.lambda" 60 $ "trySeeingIfPath for " ++ show xps
      let postpone' blocker tgt =
            ifM (isNothing <$> cubicalOption) {-then-} dontUseTargetType {-else-} $ postpone blocker tgt
      ifBlocked target postpone' $ \ _ t -> do
        ifNotM (isPathType <$> pathView t) dontUseTargetType {-else-} do
          -- Note that --cubical is on here since we returned from 'pathView'.
          checkPath (List1.head xps) typ body t

    postpone blocker tgt = flip postponeTypeCheckingProblem blocker $
      CheckExpr cmp (A.Lam A.exprNoRange (A.DomainFull b) body) tgt

    dontUseTargetType = do
      -- Checking λ (xs : argsT) → body : target
      verboseS "tc.term.lambda" 5 $ tick "lambda-no-target-type"

      -- First check that argsT is a valid type
      argsT <- workOnTypes $ isType_ typ
      let tel = namedBindsToTel1 xs argsT
      reportSDoc "tc.term.lambda" 30 $ "dontUseTargetType tel =" <+> pretty tel

      -- Andreas, 2015-05-28 Issue 1523
      -- If argsT is a SizeLt, it must be non-empty to avoid non-termination.
      -- TODO: do we need to block checkExpr?
      checkSizeLtSat $ unEl argsT

      -- Jesper 2019-12-17, #4261: we need to postpone here if
      -- checking of the record pattern fails; if we try to catch
      -- higher up the metas created during checking of @argsT@ are
      -- not available.
      let postponeOnBlockedPattern m = m `catchIlltypedPatternBlockedOnMeta` \(err , x) -> do
            reportSDoc "tc.term" 50 $ vcat $
              [ "checking record pattern stuck on meta: " <+> text (show x) ]
            t1 <- addContext (xs, argsT) $ workOnTypes newTypeMeta_
            let e    = A.Lam A.exprNoRange (A.DomainFull b) body
                tgt' = telePi tel t1
            w <- postponeTypeCheckingProblem (CheckExpr cmp e tgt') x
            return (tgt' , w)

      -- Now check body : ?t₁
      -- DONT USE tel for addContext, as it loses NameIds.
      -- WRONG: v <- addContext tel $ checkExpr body t1
      (target0 , w) <- postponeOnBlockedPattern $
         addContext (xs, argsT) $ addTypedPatterns xps $ do
           t1 <- workOnTypes newTypeMeta_
           v  <- checkExpr' cmp body t1
           return (telePi tel t1 , teleLam tel v)

      -- Do not coerce hidden lambdas
      if notVisible info || any notVisible xs then do
        pid <- newProblem_ $ leqType target0 target
        blockTermOnProblem target w pid
      else do
        coerce cmp w target0 target


    useTargetType tel@(ExtendTel dom (Abs y EmptyTel)) btyp = do
        verboseS "tc.term.lambda" 5 $ tick "lambda-with-target-type"
        reportSLn "tc.term.lambda" 30 $ "useTargetType y  = " ++ y

        let (x :| []) = xs
        unless (sameHiding dom info) $ typeError $ WrongHidingInLambda target
        when (isJust $ getNameOf x) $
          -- Andreas, 2020-03-25, issue #4481: check for correct name
          unless (namedSame dom x) $
            setCurrentRange x $ typeError $ WrongHidingInLHS
        -- Andreas, 2011-10-01 ignore relevance in lambda if not explicitly given
        info <- lambdaModalityCheck dom info
        -- Andreas, 2015-05-28 Issue 1523
        -- Ensure we are not stepping under a possibly non-existing size.
        -- TODO: do we need to block checkExpr?
        let a = unDom dom
        checkSizeLtSat $ unEl a
        -- We only need to block the final term on the argument type
        -- comparison. The body will be blocked if necessary. We still want to
        -- compare the argument types first, so we spawn a new problem for that
        -- check.
        (pid, argT) <- newProblem $ isTypeEqualTo typ a
        -- Andreas, Issue 630: take name from function type if lambda name is "_"
        v <- lambdaAddContext (namedArg x) y (defaultArgDom info argT) $
               addTypedPatterns xps $ checkExpr' cmp body btyp
        blockTermOnProblem target (Lam info $ Abs (namedArgName x) v) pid

    useTargetType _ _ = __IMPOSSIBLE__

-- | Check that modality info in lambda is compatible with modality
--   coming from the function type.
--   If lambda has no user-given modality, copy that of function type.
lambdaModalityCheck :: (LensAnnotation dom, LensModality dom) => dom -> ArgInfo -> TCM ArgInfo
lambdaModalityCheck dom = lambdaAnnotationCheck (getAnnotation dom) <=< lambdaPolarityCheck m <=< lambdaCohesionCheck m <=< lambdaQuantityCheck m <=< lambdaIrrelevanceCheck m
  where m = getModality dom

-- | Check that irrelevance info in lambda is compatible with irrelevance
--   coming from the function type.
--   If lambda has no user-given relevance, copy that of function type.
lambdaIrrelevanceCheck :: LensRelevance dom => dom -> ArgInfo -> TCM ArgInfo
lambdaIrrelevanceCheck dom info
    -- Case: no specific user annotation: use relevance of function type
  | getRelevance info == defaultRelevance = return $ setRelevance (getRelevance dom) info
    -- Case: explicit user annotation is taken seriously
  | otherwise = do
      let rPi  = getRelevance dom  -- relevance of function type
      let rLam = getRelevance info -- relevance of lambda
      unless (sameRelevance rPi rLam) $
        typeError WrongIrrelevanceInLambda
      return info

-- | Check that quantity info in lambda is compatible with quantity
--   coming from the function type.
--   If lambda has no user-given quantity, copy that of function type.
lambdaQuantityCheck :: LensQuantity dom => dom -> ArgInfo -> TCM ArgInfo
lambdaQuantityCheck dom info
    -- Case: no specific user annotation: use quantity of function type
  | noUserQuantity info = return $ setQuantity (getQuantity dom) info
    -- Case: explicit user annotation is taken seriously
  | otherwise = do
      let qPi  = getQuantity dom  -- quantity of function type
      let qLam = getQuantity info -- quantity of lambda
      unless (qPi `sameQuantity` qLam) $ do
        typeError WrongQuantityInLambda
      return info

lambdaAnnotationCheck :: LensAnnotation dom => dom -> ArgInfo -> TCM ArgInfo
lambdaAnnotationCheck dom info
    -- Case: no specific user annotation: use annotation of function type
  | getAnnotation info == defaultAnnotation = return $ setAnnotation (getAnnotation dom) info
    -- Case: explicit user annotation is taken seriously
  | otherwise = do
      let aPi  = getAnnotation dom  -- annotation of function type
      let aLam = getAnnotation info -- annotation of lambda
      unless (aPi == aLam) $ do
        typeError WrongAnnotationInLambda
      return info

-- | Check that cohesion info in lambda is compatible with cohesion
--   coming from the function type.
--   If lambda has no user-given cohesion, copy that of function type.
lambdaCohesionCheck :: LensCohesion dom => dom -> ArgInfo -> TCM ArgInfo
lambdaCohesionCheck dom info
    -- Case: no specific user annotation: use cohesion of function type
  | getCohesion info == defaultCohesion = return $ setCohesion (getCohesion dom) info
    -- Case: explicit user annotation is taken seriously
  | otherwise = do
      let cPi  = getCohesion dom  -- cohesion of function type
      let cLam = getCohesion info -- cohesion of lambda
      unless (cPi `sameCohesion` cLam) $ do
        -- if there is a cohesion annotation then
        -- it better match the domain.
        typeError WrongCohesionInLambda
      return info

-- | Check that polarity info in lambda is compatible with polarity
--   coming from the function type.
--   If lambda has no user-given polarity, copy that of function type.
lambdaPolarityCheck :: LensModalPolarity dom => dom -> ArgInfo -> TCM ArgInfo
lambdaPolarityCheck dom info
    -- Case: no specific user annotation: use polarity of function type
  | getModalPolarity info == defaultPolarity = return $ setModalPolarity (getModalPolarity dom) info
    -- Case: explicit user annotation is taken seriously
  | otherwise = do
      let cPi  = getModalPolarity dom  -- polarity of function type
      let cLam = getModalPolarity info -- polarity of lambda
      unless (cPi `samePolarity` cLam) $ do
        -- if there is a polarity annotation then
        -- it better match the domain.
        typeError WrongPolarityInLambda
      return info

-- Andreas, issue #630: take name from function type if lambda name is "_".
lambdaAddContext :: MonadAddContext m => Name -> ArgName -> Dom Type -> m a -> m a
lambdaAddContext x y dom
  | isNoName x = addContext (y, dom)                 -- Note: String instance
  | otherwise  = addContext (x, dom)                 -- Name instance of addContext

-- | Checking a lambda whose domain type has already been checked.
checkPostponedLambda :: Comparison -> Arg (List1 (WithHiding Name), Maybe Type) -> A.Expr -> Type -> TCM Term
-- checkPostponedLambda cmp args@(Arg _    ([]    , _ )) body target = do
--   checkExpr' cmp body target
checkPostponedLambda cmp args@(Arg info (WithHiding h x :| xs, mt)) body target = do
  let postpone _ t = postponeTypeCheckingProblem_ $ CheckLambda cmp args body t
      lamHiding = mappend h $ getHiding info
  insertHiddenLambdas lamHiding target postpone $ \ t@(El _ (Pi dom b)) -> do
    -- Andreas, 2011-10-01 ignore relevance in lambda if not explicitly given
    info' <- setHiding lamHiding <$> lambdaModalityCheck dom info
    -- We only need to block the final term on the argument type
    -- comparison. The body will be blocked if necessary. We still want to
    -- compare the argument types first, so we spawn a new problem for that
    -- check.
    mpid <- caseMaybe mt (return Nothing) $ \ ascribedType -> Just <$> do
      newProblem_ $ leqType (unDom dom) ascribedType
    -- We type-check the body with the ascribedType given by the user
    -- to get better error messages.
    -- Using the type dom from the usage context would be more precise,
    -- though.
    -- TODO: quantity
    let dom' = setRelevance (getRelevance info') . setHiding lamHiding $
          maybe dom (dom $>) mt
    v <- lambdaAddContext x (absName b) dom'  $
      checkPostponedLambda0 cmp (Arg info (xs, mt)) body $ absBody b
    let v' = Lam info' $ Abs (nameToArgName x) v
    maybe (return v') (blockTermOnProblem t v') mpid

checkPostponedLambda0 :: Comparison -> Arg ([WithHiding Name], Maybe Type) -> A.Expr -> Type -> TCM Term
checkPostponedLambda0 cmp (Arg _    ([]    , _ )) body target =
  checkExpr' cmp body target
checkPostponedLambda0 cmp (Arg info (x : xs, mt)) body target =
  checkPostponedLambda cmp (Arg info (x :| xs, mt)) body target


-- | Insert hidden lambda until the hiding info of the domain type
--   matches the expected hiding info.
--   Throws 'WrongHidingInLambda'
insertHiddenLambdas
  :: Hiding                       -- ^ Expected hiding.
  -> Type                         -- ^ Expected to be a function type.
  -> (Blocker -> Type -> TCM Term) -- ^ Continuation on blocked type.
  -> (Type -> TCM Term)           -- ^ Continuation when expected hiding found.
                                  --   The continuation may assume that the @Type@
                                  --   is of the form @(El _ (Pi _ _))@.
  -> TCM Term                     -- ^ Term with hidden lambda inserted.
insertHiddenLambdas h target postpone ret = do
  -- If the target type is blocked, we postpone,
  -- because we do not know if a hidden lambda needs to be inserted.
  ifBlocked target postpone $ \ _ t -> do
    case unEl t of

      Pi dom b -> do
        let h' = getHiding dom
        -- Found expected hiding: return function type.
        if sameHiding h h' then ret t else do
          -- Found a visible argument but expected a hidden one:
          -- That's an error, as we cannot insert a visible lambda.
          if visible h' then typeError $ WrongHidingInLambda target else do
            -- Otherwise, we found a hidden argument that we can insert.
            let x    = absName b
            Lam (setOrigin Inserted $ domInfo dom) . Abs x <$> do
              addContext (x, dom) $ insertHiddenLambdas h (absBody b) postpone ret

      _ -> typeError $ ShouldBePi target

-- | @checkAbsurdLambda i h e t@ checks absurd lambda against type @t@.
--   Precondition: @e = AbsurdLam i h@
checkAbsurdLambda :: Comparison -> A.ExprInfo -> Hiding -> A.Expr -> Type -> TCM Term
checkAbsurdLambda cmp i h e t =
  setRunTimeModeUnlessInHardCompileTimeMode $ do
      -- Andreas, 2019-10-01: check absurd lambdas in non-erased mode.
      -- Otherwise, they are not usable in meta-solutions in the term world.
      -- See test/Succeed/Issue3176.agda for an absurd lambda
      -- created in types.
      -- #4743: Except if hard compile-time mode is enabled.
  t <- instantiateFull t
  ifBlocked t (\ blocker t' -> postponeTypeCheckingProblem (CheckExpr cmp e t') blocker) $ \ _ t' -> do
    case unEl t' of
      Pi dom@(Dom{domInfo = info', unDom = a}) b
        | not (sameHiding h info') -> typeError $ WrongHidingInLambda t'
        | otherwise -> blockTerm t' $ do
          ensureEmptyType (getRange i) a
          -- Add helper function
          top <- currentModule
          aux <- qualify top <$> freshName_ (getRange i, absurdLambdaName)
          -- if we are in irrelevant / erased position, the helper function
          -- is added as irrelevant / erased
          mod <- currentModality
          reportSDoc "tc.term.absurd" 10 $ vcat
            [ ("Adding absurd function" <+> prettyTCM mod) <> prettyTCM aux
            , nest 2 $ "of type" <+> prettyTCM t'
            ]
          lang <- getLanguage
          fun  <- emptyFunctionData
          addConstant aux $
            (\ d -> (defaultDefn (setModality mod info') aux t' lang d)
                    { defPolarity       = [Nonvariant]
                    , defArgOccurrences = [Unused] })
            $ FunctionDefn fun
              { _funClauses        =
                  [ Clause
                    { clauseLHSRange  = getRange e
                    , clauseFullRange = getRange e
                    , clauseTel       = telFromList [fmap (absurdPatternName,) dom]
                    , namedClausePats = [Arg info' $ Named (Just $ WithOrigin Inserted $ unranged $ absName b) $ absurdP 0]
                    , clauseBody      = Nothing
                    , clauseType      = Just $ setModality mod $ defaultArg $ absBody b
                    , clauseCatchall    = True      -- absurd clauses are safe as catch-alls
                    , clauseRecursive   = Just False
                    , clauseUnreachable = Just True -- absurd clauses are unreachable
                    , clauseEllipsis    = NoEllipsis
                    , clauseWhereModule = Nothing
                    }
                  ]
              , _funCompiled       = Just $ Fail [Arg info' "()"]
              , _funSplitTree      = Just $ SplittingDone 0
              , _funMutual         = Just []
              , _funTerminates     = Just True
              , _funExtLam         = Just $ ExtLamInfo top True empty
              }
          -- Andreas 2012-01-30: since aux is lifted to toplevel
          -- it needs to be applied to the current telescope (issue 557)
          Def aux . map Apply . teleArgs <$> getContextTelescope
      _ -> typeError $ ShouldBePi t'

-- | @checkExtendedLambda i di erased qname cs e t@ check pattern matching lambda.
-- Precondition: @e = ExtendedLam i di erased qname cs@
checkExtendedLambda ::
  Comparison -> A.ExprInfo -> A.DefInfo -> Erased -> QName ->
  List1 A.Clause -> A.Expr -> Type -> TCM Term
checkExtendedLambda cmp i di erased qname cs e t = do
  mod <- currentModality
  if isErased erased && not (hasQuantity0 mod) then
    genericError $ unwords
      [ "Erased pattern-matching lambdas may only be used in erased"
      , "contexts"
      ]
   else setModeUnlessInHardCompileTimeMode erased $ do
        -- Erased pattern-matching lambdas are checked in hard
        -- compile-time mode. For non-erased pattern-matching lambdas
        -- run-time mode is used, unless the current mode is hard
        -- compile-time mode.
   -- Andreas, 2016-06-16 issue #2045
   -- Try to get rid of unsolved size metas before we
   -- fix the type of the extended lambda auxiliary function
   solveSizeConstraints DontDefaultToInfty
   lamMod <- inFreshModuleIfFreeParams currentModule  -- #2883: need a fresh module if refined params
   t <- instantiateFull t
   ifBlocked t (\ m t' -> postponeTypeCheckingProblem_ $ CheckExpr cmp e t') $ \ _ t -> do
     j   <- currentOrFreshMutualBlock
     mod <- currentModality
     let info = setModality mod defaultArgInfo

     reportSDoc "tc.term.exlam" 20 $ vcat
       [ hsep
         [ text $ show $ A.defAbstract di
         , "extended lambda's implementation"
         , doubleQuotes $ prettyTCM qname
         , "has type:"
         ]
       , prettyTCM t -- <+> " where clauses: " <+> text (show cs)
       ]
     args     <- getContextArgs

     -- Andreas, Ulf, 2016-02-02: We want to postpone type checking an extended lambda
     -- in case the lhs checker failed due to insufficient type info for the patterns.
     -- Issues 480, 1159, 1811.
     abstract (A.defAbstract di) $ do
       -- Andreas, 2013-12-28: add extendedlambda as @Function@, not as @Axiom@;
       -- otherwise, @addClause@ in @checkFunDef'@ fails (see issue 1009).
       addConstant qname =<< do
         lang <- getLanguage
         fun  <- emptyFunction
         useTerPragma $
           (defaultDefn info qname t lang fun)
             { defMutual = j }
       checkFunDef' t info (Just $ ExtLamInfo lamMod False empty) Nothing di qname $
         List1.toList cs
       whenNothingM (asksTC envMutualBlock) $
         -- Andrea 10-03-2018: Should other checks be performed here too? e.g. termination/positivity/..
         checkIApplyConfluence_ qname
       return $ Def qname $ map Apply args
  where
    -- Concrete definitions cannot use information about abstract things.
    abstract ConcreteDef = inConcreteMode
    abstract AbstractDef = inAbstractMode

-- | Run a computation.
--
--   * If successful, that's it, we are done.
--
--   * If @NotADatatype a@ or @CannotEliminateWithPattern p a@
--     is thrown and type @a@ is blocked on some meta @x@,
--     reset any changes to the state and pass (the error and) @x@ to the handler.
--
--   * If @SplitError (UnificationStuck c tel us vs _)@ is thrown and the unification
--     problem @us =?= vs : tel@ is blocked on some meta @x@ pass @x@ to the handler.
--
--   * If another error was thrown or the type @a@ is not blocked, reraise the error.
--
--   Note that the returned meta might only exists in the state where the error was
--   thrown, thus, be an invalid 'MetaId' in the current state.
--
catchIlltypedPatternBlockedOnMeta :: TCM a -> ((TCErr, Blocker) -> TCM a) -> TCM a
catchIlltypedPatternBlockedOnMeta m handle = do

  -- Andreas, 2016-07-13, issue 2028.
  -- Save the state to rollback the changes to the signature.
  st <- getTC

  m `catchError` \ err -> do

    let reraise :: MonadError TCErr m => m a
        reraise = throwError err

    -- Get the blocker responsible for the type error.
    -- If we do not find a blocker or the error should not be handled,
    -- we reraise the error.
    blocker <- maybe reraise return $ case err of
      TypeError _ s cl -> case clValue cl of
        SortOfSplitVarError b _                       -> b
        SplitError (UnificationStuck b c tel us vs _) -> b
        SplitError (BlockedType b aClosure)           -> Just b
        CannotEliminateWithPattern b p a              -> b
        -- Andrea: TODO look for blocking meta in tClosure and its Sort.
        -- SplitError (CannotCreateMissingClause _ _ _ tClosure) ->
        _                                             -> Nothing
      _ -> Nothing

    reportSDoc "tc.postpone" 20 $ vcat $
      [ "checking definition blocked on: " <+> prettyTCM blocker ]

    -- Note that we messed up the state a bit.  We might want to unroll these state changes.
    -- However, they are mostly harmless:
    -- 1. We created a new mutual block id.
    -- 2. We added a constant without definition.
    -- In fact, they are not so harmless, see issue 2028!
    -- Thus, reset the state!
    putTC st

    -- There might be metas in the blocker not known in the reset state, as they could have been
    -- created somewhere on the way to the type error.
    blocker <- (`onBlockingMetasM` blocker) $ \ x ->
                lookupMeta x >>= \ case
      -- Case: we do not know the meta, so cannot unblock.
      Nothing -> return neverUnblock
      -- Case: we know the meta here.
      -- Just m | InstV{} <- mvInstantiation m -> __IMPOSSIBLE__  -- It cannot be instantiated yet.
      -- Andreas, 2018-11-23: I do not understand why @InstV@ is necessarily impossible.
      -- The reasoning is probably that the state @st@ is more advanced that @s@
      -- in which @x@ was blocking, thus metas in @st@ should be more instantiated than
      -- in @s@.  But issue #3403 presents a counterexample, so let's play save and reraise.
      -- Ulf, 2020-08-13: But treat this case as not blocked and reraise on both always and never.
      -- Ulf, 2020-08-13: Previously we returned neverUnblock for frozen metas here, but this is in
      -- fact not very helpful. Yes there is no hope of solving the problem, but throwing a hard
      -- error means we rob the user of the tools needed to figure out why the meta has not been
      -- solved. Better to leave the constraint.
      Just Left{} -> return alwaysUnblock
      Just (Right m)
        | InstV{} <- mvInstantiation m -> return alwaysUnblock
        | otherwise                    -> return $ unblockOnMeta x

    -- If it's not blocked or we can't ever unblock reraise the error.
    if blocker `elem` [neverUnblock, alwaysUnblock] then reraise else handle (err, blocker)

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

-- | Picks up record field assignments from modules that export a definition
--   that has the same name as the missing field.

expandModuleAssigns
  :: [Either A.Assign A.ModuleName]  -- ^ Modules and field assignments.
  -> [C.Name]                        -- ^ Names of fields of the record type.
  -> TCM A.Assigns                   -- ^ Completed field assignments from modules.
expandModuleAssigns mfs xs = do
  let (fs , ms) = partitionEithers mfs

  -- The fields of the record that have not been given by field assignments @fs@
  -- are looked up in the given modules @ms@.
  fs' <- forM (xs List.\\ map (view nameFieldA) fs) $ \ f -> do

    -- Get the possible assignments for field f from the modules.
    pms <- forM ms $ \ m -> do
      modScope <- getNamedScope m
      let names :: ThingsInScope AbstractName
          names = exportedNamesInScope modScope
      return $
        case Map.lookup f names of
          Just (n :| []) -> Just (m, FieldAssignment f $ killRange $ A.nameToExpr n)
          _ -> Nothing

    -- If we have several matching assignments, that's an error.
    case catMaybes pms of
      []        -> return Nothing
      [(_, fa)] -> return (Just fa)
      x:y:zs    -> typeError $ AmbiguousField f $ fmap fst $ List2 x y zs
  return (fs ++ catMaybes fs')

-- | @checkRecordExpression fs e t@ checks record construction against type @t@.
-- Precondition @e = Rec _ fs@.
checkRecordExpression
  :: Comparison       -- ^ How do we related the inferred type of the record expression
                      --   to the expected type?  Subtype or equal type?
  -> A.RecStyle       -- ^ record {...} or record where ...
  -> A.RecordAssigns  -- ^ @mfs@: modules and field assignments.
  -> A.Expr           -- ^ Must be @A.Rec _ mfs@.
  -> Type             -- ^ Expected type of record expression.
  -> TCM Term         -- ^ Record value in internal syntax.
checkRecordExpression cmp style mfs e t = do
  reportSDoc "tc.term.rec" 10 $ sep
    [ "checking record expression"
    , prettyA e
    ]
  ifBlocked t (\ _ t -> guessRecordType t) {-else-} $ \ _ t -> do
  case unEl t of
    -- Case: We know the type of the record already.
    Def r es  -> do
      let ~(Just vs) = allApplyElims es
      reportSDoc "tc.term.rec" 20 $ "  r   = " <> pure (P.pretty r)

      def <- getRecordDef r
      let -- Field names (C.Name) with ArgInfo from record type definition.
          cxs  = map argFromDom $ recordFieldNames def
          -- Just field names.
          xs   = map unArg cxs
          -- Record constructor.
          con  = killRange $ _recConHead def
      reportSDoc "tc.term.rec" 20 $ vcat
        [ "  xs  = " <> pure (P.pretty xs)
        , "  ftel= " <> prettyTCM (_recTel def)
        , "  con = " <> pure (P.pretty con)
        ]

      -- Record expressions corresponding to erased record
      -- constructors can only be used in compile-time mode.
      constructorQ <- getQuantity <$> getConstInfo (conName con)
      currentQ     <- viewTC eQuantity
      unless (constructorQ `moreQuantity` currentQ) $
        typeError $ GenericError $
        "A record expression corresponding to an erased record " ++
        "constructor must only be used in erased settings"

      -- Andreas, 2018-09-06, issue #3122.
      -- Associate the concrete record field names used in the record expression
      -- to their counterpart in the record type definition.
      disambiguateRecordFields (map _nameFieldA $ lefts mfs) (map unDom $ _recFields def)

      -- Compute the list of given fields, decorated with the ArgInfo from the record def.
      -- Andreas, 2019-03-18, issue #3122, also pick up non-visible fields from the modules.
      fs <- expandModuleAssigns mfs xs

      -- Compute a list of metas for the missing visible fields.
      scope <- getScope
      let re = getRange e
          meta x = A.Underscore $ A.MetaInfo re scope Nothing (prettyShow x) A.UnificationMeta
      -- In @es@ omitted explicit fields are replaced by underscores.
      -- Omitted implicit or instance fields
      -- are still left out and inserted later by checkArguments_.
      es <- insertMissingFieldsWarn style r meta fs cxs

      args <- checkArguments_ cmp ExpandLast re es (_recTel def `apply` vs) >>= \case
        (elims, remainingTel) | null remainingTel
                              , Just args <- allApplyElims elims -> return args
        _ -> __IMPOSSIBLE__
      -- Don't need to block here!
      reportSDoc "tc.term.rec" 20 $ text $ "finished record expression"
      let origin = case style of
            A.RecStyleBrace -> ConORec
            A.RecStyleWhere -> ConORecWhere
      return $ Con con origin (map Apply args)
    _ -> typeError $ ShouldBeRecordType t

  where
    -- Case: We don't know the type of the record.
    guessRecordType t = do
      let fields = [ x | Left (FieldAssignment x _) <- mfs ]
      rs <- findPossibleRecords fields
      reportSDoc "tc.term.rec" 30 $ "Possible records for" <+> prettyTCM t <+> "are" <?> pretty rs
      case rs of
          -- If there are no records with the right fields we might as well fail right away.
        [] -> typeError $ NoKnownRecordWithSuchFields fields
          -- If there's only one record with the appropriate fields, go with that.
        [r] -> do
          -- #5198: Don't generate metas for parameters of the current module. In most cases they
          -- get solved, but not always.
          def <- instantiateDef =<< getConstInfo r
          ps  <- freeVarsToApply r
          let rt = defType def
          reportSDoc "tc.term.rec" 30 $ "Type of unique record" <+> prettyTCM rt
          vs  <- newArgsMeta rt
          target <- reduce $ piApply rt vs
          s  <- case unEl target of
                  Sort s  -> return s
                  v       -> do
                    reportSDoc "impossible" 10 $ vcat
                      [ "The impossible happened when checking record expression against meta"
                      , "Candidate record type r = " <+> prettyTCM r
                      , "Type of r               = " <+> prettyTCM rt
                      , "Ends in (should be sort)= " <+> prettyTCM v
                      , text $ "  Raw                   =  " ++ show v
                      ]
                    __IMPOSSIBLE__
          let inferred = El s $ Def r $ map Apply (ps ++ vs)
          v <- checkExpr e inferred
          coerce cmp v inferred t

          -- If there are more than one possible record we postpone
        _:_:_ -> do
          reportSDoc "tc.term.expr.rec" 10 $ sep
            [ "Postponing type checking of"
            , nest 2 $ prettyA e <+> ":" <+> prettyTCM t
            ]
          postponeTypeCheckingProblem_ $ CheckExpr cmp e t

-- | @checkRecordUpdate cmp ei recexpr fs e t@
--
-- Preconditions: @e = RecUpdate ei recexpr fs@ and @t@ is reduced.
--
checkRecordUpdate
  :: Comparison   -- ^ @cmp@
  -> A.RecInfo    -- ^ @ei@
  -> A.Expr       -- ^ @recexpr@
  -> A.Assigns    -- ^ @fs@
  -> A.Expr       -- ^ @e = RecUpdate ei recexpr fs@
  -> Type         -- ^ Need not be reduced.
  -> TCM Term
checkRecordUpdate cmp ei@(A.RecInfo _ style) recexpr fs eupd t = do
  ifBlocked t (\ _ _ -> tryInfer) $ {-else-} \ _ t' -> do
    caseMaybeM (isRecordType t') should $ \ (r, _pars, defn) -> do
      -- Bind the record value (before update) to a fresh @name@.
      v <- checkExpr' cmp recexpr t'
      name <- freshNoName $ getRange recexpr
      addLetBinding defaultArgInfo Inserted name v t' $ do

        let projs = map argFromDom $ _recFields defn

        -- Andreas, 2018-09-06, issue #3122.
        -- Associate the concrete record field names used in the record expression
        -- to their counterpart in the record type definition.
        disambiguateRecordFields (map _nameFieldA fs) (map unArg projs)

        -- Desugar record update expression into record expression.
        let fs' = map (\ (FieldAssignment x e) -> (x, Just e)) fs
        let axs = map argFromDom $ recordFieldNames defn
        es  <- orderFieldsWarn style r (const Nothing) axs fs'
        let es'  = zipWith (replaceFields name ei) projs es
        let erec = A.Rec ei [ Left (FieldAssignment x e) | (Arg _ x, Just e) <- zip axs es' ]
        -- Call the type checker on the desugared syntax.
        checkExpr' cmp erec t
  where
    replaceFields :: Name -> A.RecInfo -> Arg A.QName -> Maybe A.Expr -> Maybe A.Expr
    replaceFields name ei (Arg ai p) Nothing | visible ai = Just $
      -- omitted visible fields remain unchanged: @{ ...; p = p name; ...}@
      -- (hidden fields are supposed to be inferred)
      A.App
        (A.defaultAppInfo $ getRange ei)
        (A.Proj ProjSystem $ unambiguous p)
        (defaultNamedArg $ A.Var name)
    replaceFields _ _ _ me = me  -- other fields get the user-written updates

    tryInfer = do
      (_, trec) <- inferExpr recexpr
      ifBlocked trec (\ _ _ -> postpone) $ {-else-} \ _ _ -> do
        v <- checkExpr' cmp eupd trec
        coerce cmp v trec t

    postpone = postponeTypeCheckingProblem_ $ CheckExpr cmp eupd t
    should   = typeError $ ShouldBeRecordType t

---------------------------------------------------------------------------
-- * Literal
---------------------------------------------------------------------------

checkLiteral :: Literal -> Type -> TCM Term
checkLiteral lit t = do
  t' <- litType lit
  coerce CmpEq (Lit lit) t' t

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Remove top layers of scope info of expression and set the scope accordingly
--   in the 'TCState'.

scopedExpr :: A.Expr -> TCM A.Expr
scopedExpr (A.ScopedExpr scope e) = setScope scope >> scopedExpr e
scopedExpr e                      = return e

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr = checkExpr' CmpLeq

-- Andreas, 2019-10-13, issue #4125:
-- For the sake of readable types in interactive program construction,
-- avoid unnecessary unfoldings via 'reduce' in the type checker!
checkExpr'
  :: Comparison
  -> A.Expr
  -> Type        -- ^ Unreduced!
  -> TCM Term
checkExpr' cmp e t =
  verboseBracket "tc.term.expr.top" 5 "checkExpr" $
  reportResult "tc.term.expr.top" 15 (\ v -> vcat
                                              [ "checkExpr" <?> fsep [ prettyTCM e, ":", prettyTCM t ]
                                              , "  returns" <?> prettyTCM v ]) $
  traceCall (CheckExprCall cmp e t) $ localScope $ doExpandLast $ unfoldInlined =<< do
    reportSDoc "tc.term.expr.top" 15 $
        "Checking" <+> sep
          [ fsep [ prettyTCM e, ":", prettyTCM t ]
          , nest 2 $ "at " <+> (text . prettyShow =<< getCurrentRange)
          ]
    reportSDoc "tc.term.expr.top.detailed" 80 $
      "Checking" <+> fsep [ prettyTCM e, ":", text (show t) ]
    tReduced <- reduce t
    reportSDoc "tc.term.expr.top" 15 $
        "    --> " <+> prettyTCM tReduced

    e <- scopedExpr e

    irrelevantIfProp <- runBlocked (isPropM t) >>= \case
      Right True  -> do
        let mod = unitModality { modRelevance = irrelevant }
        return $ fmap dontCare . applyModalityToContext mod
      _ -> return id

    irrelevantIfProp $ tryInsertHiddenLambda e tReduced $ case e of

        A.ScopedExpr scope e -> __IMPOSSIBLE__ -- setScope scope >> checkExpr e t

        -- a meta variable without arguments: type check directly for efficiency
        A.QuestionMark i ii -> checkQuestionMark (newValueMeta' RunMetaOccursCheck) cmp t i ii
        A.Underscore i -> checkUnderscore i cmp t

        A.WithApp _ e es -> typeError $ NotImplemented "type checking of with application"

        e0@(A.App i q (Arg ai e))
          | A.Quote _ <- unScope q -> do
             if visible ai then do
               x  <- quotedName $ namedThing e
               ty <- qNameType
               coerce cmp (quoteName x) ty t
             else typeError $ CannotQuote CannotQuoteHidden

          | A.QuoteTerm _ <- unScope q -> do
             if visible ai then do
               (et, _) <- inferExpr (namedThing e)
               doQuoteTerm cmp et t
             else typeError $ CannotQuoteTerm CannotQuoteTermHidden

        A.Quote{}     -> typeError $ CannotQuote CannotQuoteNothing
        A.QuoteTerm{} -> typeError $ CannotQuoteTerm CannotQuoteTermNothing
        A.Unquote{}   -> unquoteError NakedUnquote

        A.AbsurdLam i h -> checkAbsurdLambda cmp i h e t

        A.ExtendedLam i di erased qname cs ->
          checkExtendedLambda cmp i di erased qname cs e t

        A.Lam i (A.DomainFull b) e -> checkLambda cmp b e t

        A.Lam i (A.DomainFree _ x) e0
          | isNothing (nameOf $ unArg x) && isNothing (A.binderPattern $ namedArg x) ->
              checkExpr' cmp (A.Lam i (domainFree (getArgInfo x) $ A.unBind <$> namedArg x) e0) t
          | otherwise -> __IMPOSSIBLE__

        A.Lit _ lit  -> checkLiteral lit t
        A.Let i ds e -> checkLetBindings ds $ checkExpr' cmp e t
        e@A.Pi{} -> do
            t' <- isType_ e
            let s = getSort t'
                v = unEl t'
            coerce cmp v (sort s) t

        A.Generalized s e -> do
            (_, t') <- generalizeType (Set1.toSet s) $ isType_ e
            --noFunctionsIntoSize t' t'
            let s = getSort t'
                v = unEl t'
            coerce cmp v (sort s) t

        e@A.Fun{} -> do
            t' <- isType_ e
            let s = getSort t'
                v = unEl t'
            coerce cmp v (sort s) t

        A.Rec (A.RecInfo _ style) fs -> checkRecordExpression cmp style fs e t

        A.RecUpdate ei recexpr fs -> checkRecordUpdate cmp ei recexpr fs e t

        A.DontCare e -> do
          rel <- viewTC eRelevance
          if isIrrelevant rel then dontCare <$> do
            -- resurrect variables
            applyRelevanceToContext rel $ checkExpr' cmp e t
          else
            internalError "DontCare may only appear in irrelevant contexts"

        A.Dot{} -> typeError InvalidDottedExpression

        -- Application
        _   | Application hd args <- appView e -> checkApplication cmp hd args e t

      `catchIlltypedPatternBlockedOnMeta` \ (err, x) -> do
        -- We could not check the term because the type of some pattern is blocked.
        -- It has to be blocked on some meta, so we can postpone,
        -- being sure it will be retried when a meta is solved
        -- (which might be the blocking meta in which case we actually make progress).
        reportSDoc "tc.term" 50 $ vcat $
          [ "checking pattern got stuck on meta: " <+> pretty x ]
        postponeTypeCheckingProblem (CheckExpr cmp e t) x

  where
  -- Call checkExpr with an hidden lambda inserted if appropriate,
  -- else fallback.
  tryInsertHiddenLambda
    :: A.Expr
    -> Type      -- Reduced.
    -> TCM Term
    -> TCM Term
  tryInsertHiddenLambda e tReduced fallback
    -- Insert hidden lambda if all of the following conditions are met:
    -- type is a hidden function type, {x : A} -> B or {{x : A}} -> B
    -- expression is not a lambda with the appropriate hiding yet
    | Pi (Dom{domInfo = info, unDom = a}) b <- unEl tReduced
        , let h = getHiding info
        , notVisible h
        -- expression is not a matching hidden lambda or question mark
        , not (hiddenLambdaOrHole h e)
        = do
      let proceed = doInsert (setOrigin Inserted info) $ absName b
      expandHidden <- asksTC envExpandLast
      -- If we skip the lambda insertion for an introduction,
      -- we will hit a dead end, so proceed no matter what.
      if definitelyIntroduction then proceed else
        -- #3019 and #4170: don't insert implicit lambdas in arguments to existing metas
        if expandHidden == ReallyDontExpandLast then fallback else do
        -- Andreas, 2017-01-19, issue #2412:
        -- We do not want to insert a hidden lambda if A is
        -- possibly empty type of sizes, as this will produce an error.
        reduce a >>= isSizeType >>= \case
          Just (BoundedLt u) -> ifBlocked u (\ _ _ -> fallback) $ \ _ v -> do
            ifM (checkSizeNeverZero v) proceed fallback
            `catchError` \_ -> fallback
          _ -> proceed

    | otherwise = fallback

    where
    re = getRange e
    rx = caseMaybe (rStart re) noRange $ \ pos -> posToRange pos pos

    doInsert info y = do
      x <- C.setNotInScope <$> freshName rx y
      reportSLn "tc.term.expr.impl" 15 $ "Inserting implicit lambda"
      checkExpr' cmp (A.Lam (A.ExprRange re) (domainFree info $ A.mkBinder x) e) tReduced

    hiddenLambdaOrHole h = \case
      A.AbsurdLam _ h'          -> sameHiding h h'
      A.ExtendedLam _ _ _ _ cls -> any hiddenLHS cls
      A.Lam _ bind _            -> sameHiding h bind
      A.QuestionMark{}          -> True
      _                         -> False

    hiddenLHS (A.Clause (A.LHS _ (A.LHSHead _ (a : _))) _ _ _ _) = notVisible a
    hiddenLHS _ = False

    -- Things with are definitely introductions,
    -- thus, cannot be of hidden Pi-type, unless they are hidden lambdas.
    definitelyIntroduction = case e of
      A.Lam{}        -> True
      A.AbsurdLam{}  -> True
      A.Lit{}        -> True
      A.Pi{}         -> True
      A.Fun{}        -> True
      A.Rec{}        -> True
      A.RecUpdate{}  -> True
      A.ScopedExpr{} -> __IMPOSSIBLE__
      _ -> False

---------------------------------------------------------------------------
-- * Reflection
---------------------------------------------------------------------------

doQuoteTerm :: Comparison -> Term -> Type -> TCM Term
doQuoteTerm cmp et t = do
  et'       <- etaContract =<< instantiateFull et
  case allMetasList et' of
    []  -> do
      q  <- quoteTerm et'
      ty <- el primAgdaTerm
      coerce cmp q ty t
    metas -> postponeTypeCheckingProblem (DoQuoteTerm cmp et t) $ unblockOnAllMetas $ Set.fromList metas

-- | Unquote a TCM computation in a given hole.
unquoteM :: A.Expr -> Term -> Type -> TCM ()
unquoteM tacA hole holeType = do
  tac <- applyQuantityToJudgement zeroQuantity $
    checkExpr tacA =<< (el primAgdaTerm --> el (primAgdaTCM <#> primLevelZero <@> primUnit))
  inFreshModuleIfFreeParams $ unquoteTactic tac hole holeType

-- | Run a tactic `tac : Term → TC ⊤` in a hole (second argument) of the type
--   given by the third argument. Runs the continuation if successful.
unquoteTactic :: Term -> Term -> Type -> TCM ()
unquoteTactic tac hole goal = do
  ifM (useTC stConsideringInstance) (addConstraint neverUnblock (UnquoteTactic tac hole goal)) do
  reportSDoc "tc.term.tactic" 40 $ sep
    [ "Running tactic" <+> prettyTCM tac
    , nest 2 $ "on" <+> prettyTCM hole <+> ":" <+> prettyTCM goal ]
  ok  <- runUnquoteM $ unquoteTCM tac hole
  case ok of
    Left (BlockedOnMeta oldState blocker) -> do
      putTC oldState
      let stripFreshMeta x = maybe neverUnblock (const $ unblockOnMeta x) <$> lookupLocalMeta' x
      blocker' <- onBlockingMetasM stripFreshMeta blocker
      r <- case Set.toList $ allBlockingMetas blocker' of
            x : _ -> getRange <$> lookupLocalMeta' x
            []    -> return noRange
      setCurrentRange r $
        addConstraint blocker' (UnquoteTactic tac hole goal)
    Left err -> typeError $ UnquoteFailed err
    Right _ -> return ()

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | Check an interaction point without arguments.
checkQuestionMark
  :: (Comparison -> Type -> TCM (MetaId, Term))
  -> Comparison
  -> Type            -- ^ Not reduced!
  -> A.MetaInfo
  -> InteractionId
  -> TCM Term
checkQuestionMark new cmp t0 i ii = do
  reportSDoc "tc.interaction" 20 $ sep
    [ "Found interaction point"
    , text . show =<< asksTC (^. lensIsAbstract)
    , pretty ii
    , ":"
    , prettyTCM t0
    ]
  reportSDoc "tc.interaction" 60 $ sep
    [ "Raw:"
    , text (show t0)
    ]
  checkMeta i (newQuestionMark' new ii) cmp t0 -- Andreas, 2013-05-22 use unreduced type t0!

-- | Check an underscore without arguments.
checkUnderscore :: A.MetaInfo -> Comparison -> Type -> TCM Term
checkUnderscore i = checkMeta i (newValueMetaOfKind i RunMetaOccursCheck)

-- | Type check a meta variable.
checkMeta :: A.MetaInfo -> (Comparison -> Type -> TCM (MetaId, Term)) -> Comparison -> Type -> TCM Term
checkMeta i newMeta cmp t = fst <$> checkOrInferMeta i newMeta (Just (cmp , t))

-- | Infer the type of a meta variable.
--   If it is a new one, we create a new meta for its type.
inferMeta :: A.MetaInfo -> (Comparison -> Type -> TCM (MetaId, Term)) -> TCM (Elims -> Term, Type)
inferMeta i newMeta = mapFst applyE <$> checkOrInferMeta i newMeta Nothing

-- | Type check a meta variable.
--   If its type is not given, we return its type, or a fresh one, if it is a new meta.
--   If its type is given, we check that the meta has this type, and we return the same
--   type.
checkOrInferMeta
  :: A.MetaInfo
  -> (Comparison -> Type -> TCM (MetaId, Term))
  -> Maybe (Comparison , Type)
  -> TCM (Term, Type)
checkOrInferMeta i newMeta mt = do
  case A.metaNumber i of
    Nothing -> do
      unlessNull (A.metaScope i) setScope
      (cmp , t) <- maybe ((CmpEq,) <$> workOnTypes newTypeMeta_) return mt
      (x, v) <- newMeta cmp t
      setMetaNameSuggestion x (A.metaNameSuggestion i)
      return (v, t)
    -- Rechecking an existing metavariable
    Just x -> do
      let v = MetaV x []
      reportSDoc "tc.meta.check" 20 $
        "checking existing meta " <+> prettyTCM v
      t' <- metaType x
      reportSDoc "tc.meta.check" 20 $
        nest 2 $ "of type " <+> prettyTCM t'
      case mt of
        Nothing -> return (v, t')
        Just (cmp , t) -> (,t) <$> coerce cmp v t' t

-- | Turn a domain-free binding (e.g. lambda) into a domain-full one,
--   by inserting an underscore for the missing type.
domainFree :: ArgInfo -> A.Binder' A.Name -> A.LamBinding
domainFree info x =
  A.DomainFull $ A.mkTBind r (singleton $ unnamedArg info $ fmap A.mkBindName x)
               $ A.Underscore underscoreInfo
  where
    r = getRange x
    underscoreInfo = A.MetaInfo
      { A.metaRange          = r
      , A.metaScope          = emptyScopeInfo
      , A.metaNumber         = Nothing
      , A.metaNameSuggestion = prettyShow $ A.nameConcrete $ A.binderName x
      , A.metaKind           = A.UnificationMeta
      }


-- | Check arguments whose value we already know.
--
--   This function can be used to check user-supplied parameters
--   we have already computed by inference.
--
--   Precondition: The type @t@ of the head has enough domains.

checkKnownArguments
  :: [NamedArg A.Expr]  -- ^ User-supplied arguments (hidden ones may be missing).
  -> Args               -- ^ Inferred arguments (including hidden ones).
  -> Type               -- ^ Type of the head (must be Pi-type with enough domains).
  -> TCM (Args, Type)   -- ^ Remaining inferred arguments, remaining type.
checkKnownArguments []           vs t = return (vs, t)
checkKnownArguments (arg : args) vs t = do
  (vs', t') <- setCurrentRange arg $ checkKnownArgument arg vs t
  checkKnownArguments args vs' t'

-- | Check an argument whose value we already know.

checkKnownArgument
  :: NamedArg A.Expr    -- ^ User-supplied argument.
  -> Args               -- ^ Inferred arguments (including hidden ones).
  -> Type               -- ^ Type of the head (must be Pi-type with enough domains).
  -> TCM (Args, Type)   -- ^ Remaining inferred arguments, remaining type.
checkKnownArgument arg [] _ = typeError $ InvalidProjectionParameter arg
-- Andreas, 2019-07-22, while #3353: we should use domName, not absName !!
-- WAS:
-- checkKnownArgument arg@(Arg info e) (Arg _infov v : vs) t = do
--   (dom@Dom{domInfo = info',unDom = a}, b) <- mustBePi t
--   -- Skip the arguments from vs that do not correspond to e
--   if not (sameHiding info info'
--           && (visible info || maybe True (absName b ==) (bareNameOf e)))
checkKnownArgument arg (Arg _ v : vs) t = do
  -- Skip the arguments from vs that do not correspond to e
  (dom@Dom{ unDom = a }, b) <- mustBePi t
  if not $ fromMaybe __IMPOSSIBLE__ $ fittingNamedArg arg dom
    -- Continue with the next one
    then checkKnownArgument arg vs (b `absApp` v)
    -- Found the right argument
    else do
      u <- checkNamedArg arg a
      equalTerm a u v
      return (vs, b `absApp` v)

-- | Check a single argument.

checkNamedArg :: NamedArg A.Expr -> Type -> TCM Term
checkNamedArg arg@(Arg info e0) t0 = do
  let e = namedThing e0
  let x = bareNameWithDefault "" e0
  traceCall (CheckExprCall CmpLeq e t0) $ do
    reportSDoc "tc.term.args.named" 15 $ do
        "Checking named arg" <+> sep
          [ fsep [ prettyTCM arg, ":", prettyTCM t0 ]
          ]
    reportSLn "tc.term.args.named" 75 $ "  arg = " ++ show (deepUnscope arg)
    -- Ulf, 2017-03-24: (#2172) Always treat explicit _ and ? as implicit
    -- argument (i.e. solve with unification).
    -- Andreas, 2024-03-07, issue #2829: Except when we don't.
    -- E.g. when 'insertImplicitPatSynArgs' inserted an instance underscore.
    let checkU i = checkMeta i (newMetaArg (A.metaKind i) info x) CmpLeq t0
    let checkQ = checkQuestionMark (newInteractionMetaArg info x) CmpLeq t0
    if not $ isHole e then checkExpr e t0 else localScope $ do
      -- Note: we need localScope here,
      -- as scopedExpr manipulates the scope in the state.
      -- However, we may not pull localScope over checkExpr!
      -- This is why we first test for isHole, and only do
      -- scope manipulations if we actually handle the checking
      -- of e here (and not pass it to checkExpr).
      scopedExpr e >>= \case
        A.Underscore i ->  checkU i
        A.QuestionMark i ii -> checkQ i ii
        _ -> __IMPOSSIBLE__
  where
  isHole A.Underscore{} = True
  isHole A.QuestionMark{} = True
  isHole (A.ScopedExpr _ e) = isHole e
  isHole _ = False

-- | Infer the type of an expression. Implemented by checking against a meta
--   variable.  Except for neutrals, for them a polymorphic type is inferred.
inferExpr :: A.Expr -> TCM (Term, Type)
-- inferExpr e = inferOrCheck e Nothing
inferExpr = inferExpr' DontExpandLast

inferExpr' :: ExpandHidden -> A.Expr -> TCM (Term, Type)
inferExpr' exh e = traceCall (InferExpr e) $ do
  let Application hd args = appView e
  reportSDoc "tc.infer" 30 $ vcat
    [ "inferExpr': appView of " <+> prettyA e
    , "  hd   = " <+> prettyA hd
    , "  args = " <+> prettyAs args
    ]
  reportSDoc "tc.infer" 60 $ vcat
    [ text $ "  hd (raw) = " ++ show hd
    ]
  inferApplication exh hd args e

defOrVar :: A.Expr -> Bool
defOrVar A.Var{} = True
defOrVar A.Def'{} = True
defOrVar A.Proj{} = True
defOrVar (A.ScopedExpr _ e) = defOrVar e
defOrVar _     = False

-- | Used to check aliases @f = e@.
--   Switches off 'ExpandLast' for the checking of top-level application.
checkDontExpandLast :: Comparison -> A.Expr -> Type -> TCM Term
checkDontExpandLast cmp e t = case e of
  _ | Application hd args <- appView e,  defOrVar hd ->
    traceCall (CheckExprCall cmp e t) $ localScope $ dontExpandLast $ do
      checkApplication cmp hd args e t
  _ -> checkExpr' cmp e t -- note that checkExpr always sets ExpandLast

-- | Check whether a de Bruijn index is bound by a module telescope.
isModuleFreeVar :: Int -> TCM Bool
isModuleFreeVar i = do
  params <- moduleParamsToApply =<< currentModule
  return $ any ((== Var i []) . unArg) params

-- | Infer the type of an expression, and if it is of the form
--   @{tel} -> D vs@ for some datatype @D@ then insert the hidden
--   arguments.  Otherwise, leave the type polymorphic.
inferExprForWith :: Arg A.Expr -> TCM (Term, Type)
inferExprForWith (Arg info e) = verboseBracket "tc.with.infer" 20 "inferExprForWith" $
  applyRelevanceToContext (getRelevance info) $ do
    reportSDoc "tc.with.infer" 20 $ "inferExprForWith " <+> prettyTCM e
    reportSLn  "tc.with.infer" 80 $ "inferExprForWith " ++ show (deepUnscope e)
    traceCall (InferExpr e) $ do
      -- Andreas, 2024-02-26, issue #7148:
      -- The 'instantiateFull' here performs necessary eta-contraction,
      -- both for future with-abstraction,
      -- and for testing whether v is a variable modulo eta.
      (v, t) <- instantiateFull =<< inferExpr e
      v <- reduce v
      -- Andreas 2014-11-06, issue 1342.
      -- Check that we do not `with` on a module parameter!
      case v of
        Var i [] -> whenM (isModuleFreeVar i) $ do
          reportSDoc "tc.with.infer" 80 $ vcat
            [ text $ "with expression is variable " ++ show i
            , "current modules = " <+> do text . show =<< currentModule
            , "current module free vars = " <+> do text . show =<< getCurrentModuleFreeVars
            , "context size = " <+> do text . show =<< getContextSize
            , "current context = " <+> do prettyTCM =<< getContextTelescope
            ]
          typeError $ WithOnFreeVariable e v
        _        -> return ()
      -- Possibly insert hidden arguments.
      TelV tel t0 <- telViewUpTo' (-1) (not . visible) t
      (v, t) <- case unEl t0 of
        Def d vs -> do
          isDataOrRecordType d >>= \case
            Nothing -> return (v, t)
            Just{}  -> do
              (args, t1) <- implicitArgs (-1) notVisible t
              return (v `apply` args, t1)
        _ -> return (v, t)
      -- #6868, #7113: trigger instance search to resolve instances in with-expression
      solveAwakeConstraints
      return (v, t)

---------------------------------------------------------------------------
-- * Let bindings
---------------------------------------------------------------------------

checkLetBindings :: Foldable t => t A.LetBinding -> TCM a -> TCM a
checkLetBindings = foldr ((.) . checkLetBinding) id

checkLetBinding :: A.LetBinding -> TCM a -> TCM a

checkLetBinding b@(A.LetBind i info x t e) ret =
  traceCall (CheckLetBinding b) $ do
    -- #4131: Only DontExpandLast if no user written type signature
    let check | getOrigin info == Inserted = checkDontExpandLast
              | otherwise                  = checkExpr'
    t <- workOnTypes $ isType_ t
    v <- applyModalityToContext info $ check CmpLeq e t
    addLetBinding info UserWritten (A.unBind x) v t ret

checkLetBinding b@(A.LetPatBind i p e) ret =
  traceCall (CheckLetBinding b) $ do
    p <- expandPatternSynonyms p
    (v, t) <- inferExpr' ExpandLast e
    let -- construct a type  t -> dummy  for use in checkLeftHandSide
        t0 = El (getSort t) $ Pi (defaultDom t) (NoAbs underscore __DUMMY_TYPE__)
        p0 = Arg defaultArgInfo (Named Nothing p)
    reportSDoc "tc.term.let.pattern" 10 $ vcat
      [ "let-binding pattern p at type t"
      , nest 2 $ vcat
        [ "p (A) =" <+> prettyA p
        , "t     =" <+> prettyTCM t
        , "cxtRel=" <+> do pretty =<< viewTC eRelevance
        , "cxtQnt=" <+> do pretty =<< viewTC eQuantity
        ]
      ]
    fvs <- getContextSize
    checkLeftHandSide (CheckPattern p EmptyTel t) noRange Nothing [p0] t0 Nothing [] $ \ (LHSResult _ delta0 ps _ _t _ asb _ _) -> bindAsPatterns asb $ do
          -- After dropping the free variable patterns there should be a single pattern left.
      let p = case drop fvs ps of [p] -> namedArg p; _ -> __IMPOSSIBLE__
          -- Also strip the context variables from the telescope
          delta = telFromList $ drop fvs $ telToList delta0
      reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
        [ "p (I) =" <+> prettyTCM p
        , "delta =" <+> prettyTCM delta
        , "cxtRel=" <+> do pretty =<< viewTC eRelevance
        , "cxtQnt=" <+> do pretty =<< viewTC eQuantity
        ]
      reportSDoc "tc.term.let.pattern" 80 $ nest 2 $ vcat
        [ "p (I) =" <+> (text . show) p
        ]
      -- We translate it into a list of projections.
      fs <- recordPatternToProjections p
      -- We remove the bindings for the pattern variables from the context.
      cxt0 <- getContext
      let (binds, cxt) = splitAt (size delta) cxt0
          toDrop       = length binds

          -- We create a substitution for the let-bound variables
          -- (unfortunately, we cannot refer to x in internal syntax
          -- so we have to copy v).
          sigma = map ($ v) fs
          -- We apply the types of the let bound-variables to this substitution.
          -- The 0th variable in a context is the last one, so we reverse.
          -- Further, we need to lower all other de Bruijn indices by
          -- the size of delta, so we append the identity substitution.
          sub    = parallelS (reverse sigma)

      updateContext sub (drop toDrop) $ do
        reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
          [ "delta =" <+> prettyTCM delta
          , "binds =" <+> prettyTCM binds
          ]
        let fdelta = flattenTel delta
        reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
          [ "fdelta =" <+> addContext delta (prettyTCM fdelta)
          ]
        let tsl  = applySubst sub fdelta
        -- We get a list of types
        let ts   = map unDom tsl
        -- and relevances.
        let infos = map domInfo tsl
        -- We get list of names of the let-bound vars from the context.
        let xs   = map (fst . unDom) (reverse binds)
        -- We add all the bindings to the context.
        foldr (uncurry4 $ flip addLetBinding UserWritten) ret $ List.zip4 infos xs sigma ts

checkLetBinding (A.LetApply i erased x modapp copyInfo dir) ret = do
  -- Any variables in the context that doesn't belong to the current
  -- module should go with the new module.
  -- Example: @f x y = let open M t in u@.
  -- There are 2 @new@ variables, @x@ and @y@, going into the anonynous module
  -- @module _ (x : _) (y : _) = M t@.
  fv   <- getCurrentModuleFreeVars
  n    <- getContextSize
  let new = n - fv
  reportSDoc "tc.term.let.apply" 10 $ "Applying" <+> pretty x <+> prettyA modapp <?> ("with" <+> pshow new <+> "free variables")
  reportSDoc "tc.term.let.apply" 20 $ vcat
    [ "context =" <+> (prettyTCM =<< getContextTelescope)
    , "module  =" <+> (prettyTCM =<< currentModule)
    , "fv      =" <+> text (show fv)
    ]
  checkSectionApplication i erased x modapp copyInfo
    -- Some other part of the code ensures that "open public" is
    -- ignored in let expressions. Thus there is no need for
    -- checkSectionApplication to throw an error if the import
    -- directive does contain "open public".
    dir{ publicOpen = Nothing }
  withAnonymousModule x new ret
-- LetOpen and LetDeclaredVariable are only used for highlighting.
checkLetBinding A.LetOpen{} ret = ret
checkLetBinding (A.LetDeclaredVariable _) ret = ret
