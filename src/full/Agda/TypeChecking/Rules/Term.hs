{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Term where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>), null )
#else
import Prelude hiding ( null )
#endif

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.State (get, put)
import Control.Monad.Reader

import Data.Maybe
import Data.Either (partitionEithers, lefts)
import Data.Monoid (mappend)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Generate (disambiguateRecordFields)

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Concrete.Pretty () -- only Pretty instances
import Agda.Syntax.Concrete (FieldAssignment'(..), nameFieldA)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Scope.Base ( ThingsInScope, AbstractName
                              , emptyScopeInfo
                              , exportedNamesInScope)
import Agda.Syntax.Scope.Monad (getNamedScope, freshAbstractQName)
import Agda.Syntax.Translation.InternalToAbstract (reify)

import Agda.TypeChecking.Abstract
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Generalize
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.IApplyConfluence
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Names
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
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

import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.NonemptyList
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Check that an expression is a type.
isType :: A.Expr -> Sort -> TCM Type
isType e s =
    traceCall (IsTypeCall e s) $ do
    v <- checkExpr e (sort s)
    return $ El s v

-- | Check that an expression is a type without knowing the sort.
isType_ :: A.Expr -> TCM Type
isType_ e = traceCall (IsType_ e) $ do
  let fallback = isType e =<< do workOnTypes $ newSortMeta
  case unScope e of
    A.Fun i (Arg info t) b -> do
      a <- setArgInfo info . defaultDom <$> isType_ t
      b <- isType_ b
      s <- inferFunSort (getSort a) (getSort b)
      let t' = El s $ Pi a $ NoAbs underscore b
      noFunctionsIntoSize b t'
      return t'
    A.Pi _ tel e | null tel -> isType_ e
    A.Pi _ tel e -> do
      (t0, t') <- checkPiTelescope tel $ \ tel -> do
        t0  <- instantiateFull =<< isType_ e
        tel <- instantiateFull tel
        return (t0, telePi tel t0)
      checkTelePiSort t'
      noFunctionsIntoSize t0 t'
      return t'

    -- Setᵢ
    A.Set _ n -> do
      return $ sort (mkType n)

    -- Propᵢ
    A.Prop _ n -> do
      unlessM isPropEnabled $ typeError NeedOptionProp
      return $ sort (mkProp n)

    -- Set ℓ
    A.App i s arg
      | visible arg,
        A.Set _ 0 <- unScope s -> do
      unlessM hasUniversePolymorphism $ typeError $ GenericError $
        "Use --universe-polymorphism to enable level arguments to Set"
      -- allow NonStrict variables when checking level
      --   Set : (NonStrict) Level -> Set\omega
      applyRelevanceToContext NonStrict $
        sort . Type <$> checkLevel arg

    -- Prop ℓ
    A.App i s arg
      | visible arg,
        A.Prop _ 0 <- unScope s -> do
      unlessM isPropEnabled $ typeError NeedOptionProp
      unlessM hasUniversePolymorphism $ typeError $ GenericError $
        "Use --universe-polymorphism to enable level arguments to Prop"
      applyRelevanceToContext NonStrict $
        sort . Prop <$> checkLevel arg

    -- Issue #707: Check an existing interaction point
    A.QuestionMark minfo ii -> caseMaybeM (lookupInteractionMeta ii) fallback $ \ x -> do
      -- -- | Just x <- A.metaNumber minfo -> do
      reportSDoc "tc.ip" 20 $ fsep
        [ "Rechecking meta "
        , prettyTCM x
        , text $ " for interaction point " ++ show ii
        ]
      mv <- lookupMeta x
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
noFunctionsIntoSize :: Type -> Type -> TCM ()
noFunctionsIntoSize t tBlame = do
  reportSDoc "tc.fun" 20 $ do
    let El s (Pi dom b) = tBlame
    sep [ "created function type " <+> prettyTCM tBlame
        , "with pts rule" <+> prettyTCM (getSort dom, getSort b, s)
        ]
  s <- reduce $ getSort t
  when (s == SizeUniv) $ do
    -- Andreas, 2015-02-14
    -- We have constructed a function type in SizeUniv
    -- which is illegal to prevent issue 1428.
    typeError $ FunctionTypeInSizeUniv $ unEl tBlame

-- | Check that an expression is a type which is equal to a given type.
isTypeEqualTo :: A.Expr -> Type -> TCM Type
isTypeEqualTo e0 t = scopedExpr e0 >>= \case
  A.ScopedExpr{} -> __IMPOSSIBLE__
  A.Underscore i | A.metaNumber i == Nothing -> return t
  e -> workOnTypes $ do
    t' <- isType e (getSort t)
    t' <$ leqType t t'

leqType_ :: Type -> Type -> TCM ()
leqType_ t t' = workOnTypes $ leqType t t'

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

checkGeneralizeTelescope :: A.GeneralizeTelescope -> ([Maybe Name] -> Telescope -> TCM a) -> TCM a
checkGeneralizeTelescope (A.GeneralizeTel vars tel) k =
  generalizeTelescope vars (checkTelescope tel) k

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

-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
--
--   Parametrized by a flag wether we check a typed lambda or a Pi. This flag
--   is needed for irrelevance.

checkTypedBindings :: LamOrPi -> A.TypedBinding -> (Telescope -> TCM a) -> TCM a
checkTypedBindings lamOrPi (A.TBind r xs' e) ret = do
    let xs = (map . fmap . fmap) A.unBind xs'
    -- Andreas, 2011-04-26 irrelevant function arguments may appear
    -- non-strictly in the codomain type
    -- 2011-10-04 if flag --experimental-irrelevance is set
    experimental <- optExperimentalIrrelevance <$> pragmaOptions
    t <- modEnv lamOrPi $ isType_ e

    -- Jesper, 2019-02-12, Issue #3534: warn if the type of an
    -- instance argument does not have the right shape
    unlessNull (filter isInstance xs') $ \ixs -> do
      (tel, target) <- getOutputTypeName t
      case target of
        OutputTypeName{} -> return ()
        OutputTypeVar{}  -> return ()
        OutputTypeVisiblePi{} -> warning . InstanceArgWithExplicitArg =<< prettyTCM (A.TBind r ixs e)
        OutputTypeNameNotYetKnown{} -> return ()
        NoOutputTypeName -> warning . InstanceNoOutputTypeName =<< prettyTCM (A.TBind r ixs e)

    let xs' = (map . mapRelevance) (modRel lamOrPi experimental) xs
    addContext (xs', t) $
      ret $ namedBindsToTel xs t
    where
        -- if we are checking a typed lambda, we resurrect before we check the
        -- types, but do not modify the new context entries
        -- otherwise, if we are checking a pi, we do not resurrect, but
        -- modify the new context entries
        modEnv LamNotPi = workOnTypes
        modEnv _        = id
        modRel PiNotLam xp = if xp then irrToNonStrict else id
        modRel _        _  = id
checkTypedBindings lamOrPi (A.TLet _ lbs) ret = do
    checkLetBindings lbs (ret EmptyTel)

ifPath :: Type -> TCM a -> TCM a -> TCM a
ifPath ty fallback work = do
  pv <- pathView ty
  if isPathType pv then work else fallback

checkPath :: A.TypedBinding -> A.Expr -> Type -> TCM Term
checkPath b@(A.TBind _ [x'] typ) body ty = do
    let x    = (fmap . fmap) A.unBind x'
        info = getArgInfo x
    PathType s path level typ lhs rhs <- pathView ty
    interval <- elInf primInterval
    v <- addContext ([x], interval) $
           checkExpr body (El (raise 1 s) (raise 1 (unArg typ) `apply` [argN $ var 0]))
    iZero <- primIZero
    iOne  <- primIOne
    let lhs' = subst 0 iZero v
        rhs' = subst 0 iOne  v
    let t = Lam info $ Abs (namedArgName x) v
    let btyp i = El s (unArg typ `apply` [argN i])
    locallyTC eRange (const noRange) $ blockTerm ty $ traceCall (SetRange $ getRange body) $ do
      equalTerm (btyp iZero) lhs' (unArg lhs)
      equalTerm (btyp iOne) rhs' (unArg rhs)
      return t
checkPath b body ty = __IMPOSSIBLE__
---------------------------------------------------------------------------
-- * Lambda abstractions
---------------------------------------------------------------------------

-- | Type check a lambda expression.
--   "checkLambda bs e ty"  means  (\ bs -> e) : ty
checkLambda :: Comparison -> A.TypedBinding -> A.Expr -> Type -> TCM Term
checkLambda cmp (A.TLet _ lbs) body target =
  checkLetBindings lbs (checkExpr body target)
checkLambda cmp b@(A.TBind _ xs' typ) body target = do
  reportSLn "tc.term.lambda" 60 $ "checkLambda   xs = " ++ prettyShow xs
  let numbinds = length xs
      possiblePath = numbinds == 1
                   && (case unScope typ of
                         A.Underscore{} -> True
                         _              -> False)
                   && isRelevant info && visible info
  reportSLn "tc.term.lambda" 60 $ "possiblePath = " ++ show (possiblePath, numbinds, unScope typ, info)
  TelV tel btyp <- telViewUpTo numbinds target
  if size tel < numbinds || numbinds /= 1
    then (if possiblePath then trySeeingIfPath else dontUseTargetType)
    else useTargetType tel btyp
  where
    xs = (map . fmap . fmap) A.unBind xs'
    info : _ = map getArgInfo xs
    trySeeingIfPath = do
      cubical <- optCubical <$> pragmaOptions
      reportSLn "tc.term.lambda" 60 $ "trySeeingIfPath for " ++ show xs
      let postpone' = if cubical then postpone else \ _ _ -> dontUseTargetType
      ifBlockedType target postpone' $ \ _ t -> do
          ifPath t dontUseTargetType $
            if cubical then checkPath b body t
                       else typeError $ GenericError $ "Option --cubical needed to build a path with a lambda abstraction"

    postpone m tgt = postponeTypeCheckingProblem_ $
      CheckExpr cmp (A.Lam A.exprNoRange (A.DomainFull b) body) tgt

    dontUseTargetType = do
      -- Checking λ (xs : argsT) → body : target
      verboseS "tc.term.lambda" 5 $ tick "lambda-no-target-type"

      -- First check that argsT is a valid type
      argsT <- workOnTypes $ isType_ typ
      -- Andreas, 2015-05-28 Issue 1523
      -- If argsT is a SizeLt, it must be non-empty to avoid non-termination.
      -- TODO: do we need to block checkExpr?
      checkSizeLtSat $ unEl argsT

      -- In order to have as much type information as possible when checking
      -- body, we first unify (xs : argsT) → ?t₁ with the target type. If this
      -- is inconclusive we need to block the resulting term so we create a
      -- fresh problem for the check.
      let tel = namedBindsToTel xs argsT
      reportSDoc "tc.term.lambda" 60 $ "dontUseTargetType tel =" <+> pretty tel
      -- DONT USE tel for addContext, as it loses NameIds.
      -- WRONG: t1 <- addContext tel $ workOnTypes newTypeMeta_
      t1 <- addContext (xs, argsT) $ workOnTypes newTypeMeta_
      -- Do not coerce hidden lambdas
      if notVisible info || any notVisible xs then do
        pid <- newProblem_ $ leqType (telePi tel t1) target
        -- Now check body : ?t₁
        -- WRONG: v <- addContext tel $ checkExpr body t1
        v <- addContext (xs, argsT) $ checkExpr' cmp body t1
        -- Block on the type comparison
        blockTermOnProblem target (teleLam tel v) pid
       else do
        -- Now check body : ?t₁
        -- WRONG: v <- addContext tel $ checkExpr body t1
        v <- addContext (xs, argsT) $ checkExpr' cmp body t1
        -- Block on the type comparison
        coerce cmp (teleLam tel v) (telePi tel t1) target

    useTargetType tel@(ExtendTel dom (Abs y EmptyTel)) btyp = do
        verboseS "tc.term.lambda" 5 $ tick "lambda-with-target-type"
        reportSLn "tc.term.lambda" 60 $ "useTargetType y  = " ++ y

        let [x] = xs
        unless (sameHiding dom info) $ typeError $ WrongHidingInLambda target
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
        v <- lambdaAddContext (namedArg x) y (defaultArgDom info argT) $ checkExpr' cmp body btyp
        blockTermOnProblem target (Lam info $ Abs (namedArgName x) v) pid

    useTargetType _ _ = __IMPOSSIBLE__

-- | Check that modality info in lambda is compatible with modality
--   coming from the function type.
--   If lambda has no user-given modality, copy that of function type.
lambdaModalityCheck :: LensModality dom => dom -> ArgInfo -> TCM ArgInfo
lambdaModalityCheck dom = lambdaQuantityCheck m <=< lambdaIrrelevanceCheck m
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
        -- Andreas, 2017-01-24, issue #2429
        -- we should report an error if we try to check a relevant function
        -- against an irrelevant function type (subtyping violation)
      unless (moreRelevant rPi rLam) $ do
        -- @rLam == Relevant@ is impossible here
        -- @rLam == Irrelevant@ is impossible here (least relevant)
        -- this error can only happen if @rLam == NonStrict@ and @rPi == Irrelevant@
        unless (rLam == NonStrict) __IMPOSSIBLE__  -- separate tests for separate line nums
        unless (rPi == Irrelevant) __IMPOSSIBLE__
        typeError WrongIrrelevanceInLambda
      return info

-- | Check that quantity info in lambda is compatible with quantity
--   coming from the function type.
--   If lambda has no user-given quantity, copy that of function type.
lambdaQuantityCheck :: LensQuantity dom => dom -> ArgInfo -> TCM ArgInfo
lambdaQuantityCheck dom info
    -- Case: no specific user annotation: use quantity of function type
  | getQuantity info == defaultQuantity = return $ setQuantity (getQuantity dom) info
    -- Case: explicit user annotation is taken seriously
  | otherwise = do
      let qPi  = getQuantity dom  -- quantity of function type
      let qLam = getQuantity info -- quantity of lambda
      unless (moreQuantity qPi qLam) $ do
        -- the expected use qPi cannot be unrestricted
        when (qPi == Quantityω) __IMPOSSIBLE__
        typeError WrongQuantityInLambda
      return info

lambdaAddContext :: Name -> ArgName -> Dom Type -> TCM a -> TCM a
lambdaAddContext x y dom
  | isNoName x = addContext (y, dom)                 -- Note: String instance
  | otherwise  = addContext (x, dom)                 -- Name instance of addContext

-- | Checking a lambda whose domain type has already been checked.
checkPostponedLambda :: Comparison -> Arg ([WithHiding Name], Maybe Type) -> A.Expr -> Type -> TCM Term
checkPostponedLambda cmp args@(Arg _    ([]    , _ )) body target = do
  checkExpr' cmp body target
checkPostponedLambda cmp args@(Arg info (WithHiding h x : xs, mt)) body target = do
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
    let dom' = setRelevance (getRelevance info') . setHiding lamHiding $
          maybe dom (dom $>) mt
    v <- lambdaAddContext x (absName b) dom'  $
      checkPostponedLambda cmp (Arg info (xs, mt)) body $ absBody b
    let v' = Lam info' $ Abs (nameToArgName x) v
    maybe (return v') (blockTermOnProblem t v') mpid


-- | Insert hidden lambda until the hiding info of the domain type
--   matches the expected hiding info.
--   Throws 'WrongHidingInLambda'
insertHiddenLambdas
  :: Hiding                       -- ^ Expected hiding.
  -> Type                         -- ^ Expected to be a function type.
  -> (MetaId -> Type -> TCM Term) -- ^ Continuation on blocked type.
  -> (Type -> TCM Term)           -- ^ Continuation when expected hiding found.
                                  --   The continuation may assume that the @Type@
                                  --   is of the form @(El _ (Pi _ _))@.
  -> TCM Term                     -- ^ Term with hidden lambda inserted.
insertHiddenLambdas h target postpone ret = do
  -- If the target type is blocked, we postpone,
  -- because we do not know if a hidden lambda needs to be inserted.
  ifBlockedType target postpone $ \ _ t -> do
    case unEl t of

      Pi dom b -> do
        let h' = getHiding dom
        -- Found expected hiding: return function type.
        if sameHiding h h' then ret t else do
          -- Found a visible argument but expected a hidden one:
          -- That's an error, as we cannot insert a visible lambda.
          if visible h' then typeError $ WrongHidingInLambda target else do
            -- Otherwise, we found a hidden argument that we can insert.
            let x = absName b
            Lam (domInfo dom) . Abs x <$> do
              addContext (x, dom) $ insertHiddenLambdas h (absBody b) postpone ret

      _ -> typeError . GenericDocError =<< do
        "Expected " <+> prettyTCM target <+> " to be a function type"

-- | @checkAbsurdLambda i h e t@ checks absurd lambda against type @t@.
--   Precondition: @e = AbsurdLam i h@
checkAbsurdLambda :: Comparison -> A.ExprInfo -> Hiding -> A.Expr -> Type -> TCM Term
checkAbsurdLambda cmp i h e t = do
  t <- instantiateFull t
  ifBlockedType t (\ m t' -> postponeTypeCheckingProblem_ $ CheckExpr cmp e t') $ \ _ t' -> do
    case unEl t' of
      Pi dom@(Dom{domInfo = info', unDom = a}) b
        | not (sameHiding h info') -> typeError $ WrongHidingInLambda t'
        | not (null $ allMetas a) ->
            postponeTypeCheckingProblem (CheckExpr cmp e t') $
              null . allMetas <$> instantiateFull a
        | otherwise -> blockTerm t' $ do
          ensureEmptyType (getRange i) a
          -- Add helper function
          top <- currentModule
          aux <- qualify top <$> freshName_ (getRange i, absurdLambdaName)
          -- if we are in irrelevant position, the helper function
          -- is added as irrelevant
          rel <- asksTC envRelevance
          reportSDoc "tc.term.absurd" 10 $ vcat
            [ "Adding absurd function" <+> prettyTCM rel <> prettyTCM aux
            , nest 2 $ "of type" <+> prettyTCM t'
            ]
          addConstant aux $
            (\ d -> (defaultDefn (setRelevance rel info') aux t' d)
                    { defPolarity       = [Nonvariant]
                    , defArgOccurrences = [Unused] })
            $ emptyFunction
              { funClauses        =
                  [ Clause
                    { clauseLHSRange  = getRange e
                    , clauseFullRange = getRange e
                    , clauseTel       = telFromList [fmap (absurdPatternName,) dom]
                    , namedClausePats = [Arg info' $ Named (Just $ unranged $ absName b) $ VarP PatOAbsurd (DBPatVar absurdPatternName 0)]
                    , clauseBody      = Nothing
                    , clauseType      = Just $ setRelevance rel $ defaultArg $ absBody b
                    , clauseCatchall  = False
                    , clauseUnreachable = Just True -- absurd clauses are unreachable
                    }
                  ]
              , funCompiled       = Just Fail
              , funSplitTree      = Just $ SplittingDone 0
              , funMutual         = Just []
              , funTerminates     = Just True
              }
          -- Andreas 2012-01-30: since aux is lifted to toplevel
          -- it needs to be applied to the current telescope (issue 557)
          tel <- getContextTelescope
          return $ Def aux $ map Apply $ teleArgs tel
      _ -> typeError $ ShouldBePi t'

-- | @checkExtendedLambda i di qname cs e t@ check pattern matching lambda.
-- Precondition: @e = ExtendedLam i di qname cs@
checkExtendedLambda :: Comparison -> A.ExprInfo -> A.DefInfo -> QName -> [A.Clause] ->
                       A.Expr -> Type -> TCM Term
checkExtendedLambda cmp i di qname cs e t = do
   -- Andreas, 2016-06-16 issue #2045
   -- Try to get rid of unsolved size metas before we
   -- fix the type of the extended lambda auxiliary function
   solveSizeConstraints DontDefaultToInfty
   lamMod <- inFreshModuleIfFreeParams currentModule  -- #2883: need a fresh module if refined params
   t <- instantiateFull t
   ifBlockedType t (\ m t' -> postponeTypeCheckingProblem_ $ CheckExpr cmp e t') $ \ _ t -> do
     j   <- currentOrFreshMutualBlock
     rel <- asksTC envRelevance
     let info = setRelevance rel defaultArgInfo

     reportSDoc "tc.term.exlam" 20 $
       text (show $ A.defAbstract di) <+>
       "extended lambda's implementation \"" <> prettyTCM qname <>
       "\" has type: " $$ prettyTCM t -- <+> " where clauses: " <+> text (show cs)
     args     <- getContextArgs

     -- Andreas, Ulf, 2016-02-02: We want to postpone type checking an extended lambda
     -- in case the lhs checker failed due to insufficient type info for the patterns.
     -- Issues 480, 1159, 1811.
     (abstract (A.defAbstract di) $ do
       -- Andreas, 2013-12-28: add extendedlambda as @Function@, not as @Axiom@;
       -- otherwise, @addClause@ in @checkFunDef'@ fails (see issue 1009).
       addConstant qname =<< do
         useTerPragma $
           (defaultDefn info qname t emptyFunction) { defMutual = j }
       checkFunDef' t info NotDelayed (Just $ ExtLamInfo lamMod Nothing) Nothing di qname cs
       whenNothingM (asksTC envMutualBlock) $
         -- Andrea 10-03-2018: Should other checks be performed here too? e.g. termination/positivity/..
         checkIApplyConfluence_ qname
       return $ Def qname $ map Apply args)
  where
    -- Concrete definitions cannot use information about abstract things.
    abstract ConcreteDef = inConcreteMode
    abstract AbstractDef = inAbstractMode

-- | Run a computation.
--
--   * If successful, that's it, we are done.
--
--   * If @IlltypedPattern p a@, @NotADatatype a@ or @CannotEliminateWithPattern p a@
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
catchIlltypedPatternBlockedOnMeta :: TCM a -> ((TCErr, MetaId) -> TCM a) -> TCM a
catchIlltypedPatternBlockedOnMeta m handle = do

  -- Andreas, 2016-07-13, issue 2028.
  -- Save the state to rollback the changes to the signature.
  st <- getTC

  m `catchError` \ err -> do

    let reraise = throwError err

    -- Get the blocking meta responsible for the type error.
    -- If we do not find such a meta or the error should not be handled,
    -- we reraise the error.
    x <- maybe reraise return =<< do
      case err of
        TypeError s cl -> localTCState $ do
          putTC s
          enterClosure cl $ \case
            IlltypedPattern p a -> isBlockedType a

            SplitError (UnificationStuck c tel us vs _) -> do
              -- Andreas, 2018-11-23, re issue #3403
              -- The following computation of meta-variables and picking
              -- of the first one, seems a bit brittle.
              -- I do not understand why there is a single @reduce@ here
              -- (seems to archieve a bit along @normalize@, but how much??).
              problem <- reduce =<< instantiateFull (flattenTel tel, us, vs)
              -- over-approximating the set of metas actually blocking unification
              return $ listToMaybe $ allMetas problem

            SplitError (NotADatatype aClosure) ->
              enterClosure aClosure $ \ a -> isBlockedType a

            -- Andrea: TODO look for blocking meta in tClosure and its Sort.
            -- SplitError (CannotCreateMissingClause _ _ _ tClosure) ->

            CannotEliminateWithPattern p a -> isBlockedType a

            _ -> return Nothing
        _ -> return Nothing

    reportSDoc "tc.postpone" 20 $ vcat $
      [ "checking definition blocked on meta: " <+> prettyTCM x ]

    -- Note that we messed up the state a bit.  We might want to unroll these state changes.
    -- However, they are mostly harmless:
    -- 1. We created a new mutual block id.
    -- 2. We added a constant without definition.
    -- In fact, they are not so harmless, see issue 2028!
    -- Thus, reset the state!
    putTC st

    -- The meta might not be known in the reset state, as it could have been created
    -- somewhere on the way to the type error.
    lookupMeta' x >>= \case
      -- Case: we do not know the meta, so we reraise.
      Nothing -> reraise
      -- Case: we know the meta here.
      -- Andreas, 2018-11-23: I do not understand why @InstV@ is necessarily impossible.
      -- The reasoning is probably that the state @st@ is more advanced that @s@
      -- in which @x@ was blocking, thus metas in @st@ should be more instantiated than
      -- in @s@.  But issue #3403 presents a counterexample, so let's play save and reraise
      -- Just m | InstV{} <- mvInstantiation m -> __IMPOSSIBLE__  -- It cannot be instantiated yet.
      Just m | InstV{} <- mvInstantiation m -> reraise
      -- Case: the meta is frozen (and not an interaction meta).
      -- Postponing doesn't make sense, so we reraise.
      Just m | Frozen  <- mvFrozen m -> isInteractionMeta x >>= \case
        Nothing -> reraise
      -- Remaining cases: the meta is known and can still be instantiated.
        Just{}  -> handle (err, x)
      Just{} -> handle (err, x)

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

-- | Picks up record field assignments from modules that export a definition
--   that has the same name as the missing field.

expandModuleAssigns
  :: [Either A.Assign A.ModuleName]  -- ^ Modules and field assignments.
  -> [C.Name]                        -- ^ Names of fields of the record type.
  -> TCM A.Assigns                   -- ^ Completed field assignments from modules.
expandModuleAssigns mfs exs = do
  let (fs , ms) = partitionEithers mfs
      -- The visible fields of the record that have not been given by field assignments.
      exs' = exs List.\\ map (view nameFieldA) fs

  -- Getting assignments for the missing visible fields.
  fs' <- forM exs' $ \ f -> do

    -- Get the possible assignments for field f from the modules.
    pms <- forM ms $ \ m -> do
       modScope <- getNamedScope m
       let names :: ThingsInScope AbstractName
           names = exportedNamesInScope modScope
       return $
        case Map.lookup f names of
          Just [n] -> Just (m, FieldAssignment f (A.nameExpr n))
          _        -> Nothing

    -- If we have several matching assignments, that's an error.
    case catMaybes pms of
      []        -> return Nothing
      [(_, fa)] -> return (Just fa)
      mfas      -> typeError . GenericDocError =<< do
        vcat $
          [ "Ambiguity: the field" <+> prettyTCM f
            <+> "appears in the following modules: " ]
          ++ map (prettyTCM . fst) mfas
  return (fs ++ catMaybes fs')

-- | @checkRecordExpression fs e t@ checks record construction against type @t@.
-- Precondition @e = Rec _ fs@.
checkRecordExpression
  :: Comparison       -- ^ How do we related the inferred type of the record expression
                      --   to the expected type?  Subtype or equal type?
  -> A.RecordAssigns  -- ^ @mfs@: modules and field assignments.
  -> A.Expr           -- ^ Must be @A.Rec _ mfs@.
  -> Type             -- ^ Expected type of record expression.
  -> TCM Term         -- ^ Record value in internal syntax.
checkRecordExpression cmp mfs e t = do
  reportSDoc "tc.term.rec" 10 $ sep
    [ "checking record expression"
    , prettyA e
    ]
  ifBlockedType t (\ _ t -> guessRecordType t) {-else-} $ \ _ t -> do
  case unEl t of
    -- Case: We know the type of the record already.
    Def r es  -> do
      let ~(Just vs) = allApplyElims es
      reportSDoc "tc.term.rec" 20 $ text $ "  r   = " ++ prettyShow r

      reportSDoc "tc.term.rec" 30 $ "  xs  = " <> do
        text =<< prettyShow . map unArg <$> getRecordFieldNames r
      reportSDoc "tc.term.rec" 30 $ "  ftel= " <> do
        prettyTCM =<< getRecordFieldTypes r
      reportSDoc "tc.term.rec" 30 $ "  con = " <> do
        text =<< prettyShow <$> getRecordConstructor r

      def <- getRecordDef r
      let -- Field names (C.Name) with ArgInfo from record type definition.
          cxs  = recordFieldNames def
          -- Just field names.
          xs   = map unArg cxs
          -- Record constructor.
          con  = killRange $ recConHead def
      reportSDoc "tc.term.rec" 20 $ vcat
        [ "  xs  = " <> return (P.pretty xs)
        , "  ftel= " <> prettyTCM (recTel def)
        , "  con = " <> return (P.pretty con)
        ]

      -- Andreas, 2018-09-06, issue #3122.
      -- Associate the concrete record field names used in the record expression
      -- to their counterpart in the record type definition.
      disambiguateRecordFields (map _nameFieldA $ lefts mfs) (map unArg $ recFields def)

      -- Compute the list of given fields, decorated with the ArgInfo from the record def.
      -- Andreas, 2019-03-18, issue #3122, also pick up non-visible fields from the modules.
      fs <- expandModuleAssigns mfs (map unArg cxs)

      -- Compute a list of metas for the missing visible fields.
      scope <- getScope
      let re = getRange e
          meta x = A.Underscore $ A.MetaInfo re scope Nothing (prettyShow x)
      -- In @es@ omitted explicit fields are replaced by underscores.
      -- Omitted implicit or instance fields
      -- are still left out and inserted later by checkArguments_.
      es <- insertMissingFields r meta fs cxs

      args <- checkArguments_ ExpandLast re es (recTel def `apply` vs) >>= \case
        (elims, remainingTel) | null remainingTel
                              , Just args <- allApplyElims elims -> return args
        _ -> __IMPOSSIBLE__
      -- Don't need to block here!
      reportSDoc "tc.term.rec" 20 $ text $ "finished record expression"
      return $ Con con ConORec (map Apply args)
    _         -> typeError $ ShouldBeRecordType t

  where
    -- Case: We don't know the type of the record.
    guessRecordType t = do
      let fields = [ x | Left (FieldAssignment x _) <- mfs ]
      rs <- findPossibleRecords fields
      case rs of
          -- If there are no records with the right fields we might as well fail right away.
        [] -> case fields of
          []  -> typeError $ GenericError "There are no records in scope"
          [f] -> typeError $ GenericError $ "There is no known record with the field " ++ prettyShow f
          _   -> typeError $ GenericError $ "There is no known record with the fields " ++ unwords (map prettyShow fields)
          -- If there's only one record with the appropriate fields, go with that.
        [r] -> do
          def <- getConstInfo r
          let rt = defType def
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
          let inferred = El s $ Def r $ map Apply vs
          v <- checkExpr e inferred
          coerce cmp v inferred t
          -- Andreas 2012-04-21: OLD CODE, WRONG DIRECTION, I GUESS:
          -- blockTerm t $ v <$ leqType_ t inferred

          -- If there are more than one possible record we postpone
        _:_:_ -> do
          reportSDoc "tc.term.expr.rec" 10 $ sep
            [ "Postponing type checking of"
            , nest 2 $ prettyA e <+> ":" <+> prettyTCM t
            ]
          postponeTypeCheckingProblem_ $ CheckExpr cmp e t

-- | @checkRecordUpdate ei recexpr fs e t@
-- Precondition @e = RecUpdate ei recexpr fs@.
checkRecordUpdate :: Comparison -> A.ExprInfo -> A.Expr -> A.Assigns -> A.Expr -> Type -> TCM Term
checkRecordUpdate cmp ei recexpr fs e t = do
  case unEl t of
    Def r vs  -> do
      v <- checkExpr' cmp recexpr t
      name <- freshNoName (getRange recexpr)
      addLetBinding defaultArgInfo name v t $ do
        projs <- recFields <$> getRecordDef r

        -- Andreas, 2018-09-06, issue #3122.
        -- Associate the concrete record field names used in the record expression
        -- to their counterpart in the record type definition.
        disambiguateRecordFields (map _nameFieldA fs) (map unArg projs)

        xs <- map unArg <$> getRecordFieldNames r
        es <- orderFields r Nothing xs $ map (\ (FieldAssignment x e) -> (x, Just e)) fs
        let es' = zipWith (replaceFields name ei) projs es
        checkExpr' cmp (A.Rec ei [ Left (FieldAssignment x e) | (x, Just e) <- zip xs es' ]) t

    MetaV _ _ -> do
      inferred <- inferExpr recexpr >>= reduce . snd
      case unEl inferred of
        MetaV _ _ -> postponeTypeCheckingProblem_ $ CheckExpr cmp e t
        _         -> do
          v <- checkExpr' cmp e inferred
          coerce cmp v inferred t
    _         -> typeError $ ShouldBeRecordType t
  where
    replaceFields :: Name -> A.ExprInfo -> Arg A.QName -> Maybe A.Expr -> Maybe A.Expr
    replaceFields n ei a@(Arg _ p) Nothing | visible a =
        Just $ A.App (A.defaultAppInfo $ getRange ei) (A.Def p) $ defaultNamedArg $ A.Var n
    replaceFields _ _  (Arg _ _) Nothing  = Nothing
    replaceFields _ _  _         (Just e) = Just $ e

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

checkExpr' :: Comparison -> A.Expr -> Type -> TCM Term
checkExpr' cmp e t0 =
  verboseBracket "tc.term.expr.top" 5 "checkExpr" $
  traceCall (CheckExprCall cmp e t0) $ localScope $ doExpandLast $ unfoldInlined =<< do
    reportSDoc "tc.term.expr.top" 15 $
        "Checking" <+> sep
          [ fsep [ prettyTCM e, ":", prettyTCM t0 ]
          , nest 2 $ "at " <+> (text . prettyShow =<< getCurrentRange)
          ]
    reportSDoc "tc.term.expr.top.detailed" 80 $
      "Checking" <+> fsep [ prettyTCM e, ":", text (show t0) ]
    t <- reduce t0
    reportSDoc "tc.term.expr.top" 15 $
        "    --> " <+> prettyTCM t

    e <- scopedExpr e

    tryInsertHiddenLambda e t $ case e of

        A.ScopedExpr scope e -> __IMPOSSIBLE__ -- setScope scope >> checkExpr e t

        -- a meta variable without arguments: type check directly for efficiency
        A.QuestionMark i ii -> checkQuestionMark (newValueMeta' RunMetaOccursCheck) t0 i ii
        A.Underscore i -> checkUnderscore t0 i

        A.WithApp _ e es -> typeError $ NotImplemented "type checking of with application"

        -- check |- Set l : t  (requires universe polymorphism)
        A.App i s arg@(Arg ai l)
          | A.Set _ 0 <- unScope s, visible ai ->
          ifNotM hasUniversePolymorphism
              (typeError $ GenericError "Use --universe-polymorphism to enable level arguments to Set")
          $ {- else -} do
            -- allow NonStrict variables when checking level
            --   Set : (NonStrict) Level -> Set\omega
            n <- applyRelevanceToContext NonStrict $ checkLevel arg
            -- check that Set (l+1) <= t
            reportSDoc "tc.univ.poly" 10 $
              "checking Set " <+> prettyTCM n <+>
              "against" <+> prettyTCM t
            coerce cmp (Sort $ Type n) (sort $ Type $ levelSuc n) t

        -- check |- Prop l : t  (requires universe polymorphism)
        A.App i s arg@(Arg ai l)
          | A.Prop _ 0 <- unScope s, visible ai ->
          ifNotM hasUniversePolymorphism
              (typeError $ GenericError "Use --universe-polymorphism to enable level arguments to Prop")
          $ {- else -} do
            n <- applyRelevanceToContext NonStrict $ checkLevel arg
            reportSDoc "tc.univ.poly" 10 $
              "checking Prop " <+> prettyTCM n <+>
              "against" <+> prettyTCM t
            coerce cmp (Sort $ Prop n) (sort $ Type $ levelSuc n) t

        e0@(A.App i q (Arg ai e))
          | A.Quote _ <- unScope q, visible ai -> do
          let quoted (A.Def x) = return x
              quoted (A.Macro x) = return x
              quoted (A.Proj o p) | Just x <- getUnambiguous p = return x
              quoted (A.Proj o p)  =
                typeError $ GenericError $ "quote: Ambigous name: " ++ prettyShow (unAmbQ p)
              quoted (A.Con c) | Just x <- getUnambiguous c = return x
              quoted (A.Con c)  =
                typeError $ GenericError $ "quote: Ambigous name: " ++ prettyShow (unAmbQ c)
              quoted (A.ScopedExpr _ e) = quoted e
              quoted _                  =
                typeError $ GenericError $ "quote: not a defined name"
          x <- quoted (namedThing e)
          ty <- qNameType
          coerce cmp (quoteName x) ty t

          | A.QuoteTerm _ <- unScope q -> do
             (et, _) <- inferExpr (namedThing e)
             doQuoteTerm cmp et t

        A.Quote _ -> typeError $ GenericError "quote must be applied to a defined name"
        A.QuoteTerm _ -> typeError $ GenericError "quoteTerm must be applied to a term"
        A.Unquote _ -> typeError $ GenericError "unquote must be applied to a term"

        A.AbsurdLam i h -> checkAbsurdLambda cmp i h e t

        A.ExtendedLam i di qname cs -> checkExtendedLambda cmp i di qname cs e t

        A.Lam i (A.DomainFull b) e -> checkLambda cmp b e t

        A.Lam i (A.DomainFree x) e0
          | isNothing (nameOf $ unArg x) -> checkExpr' cmp (A.Lam i (domainFree (getArgInfo x) $ A.unBind $ namedArg x) e0) t
          | otherwise -> typeError $ NotImplemented "named arguments in lambdas"

        A.Lit lit    -> checkLiteral lit t
        A.Let i ds e -> checkLetBindings ds $ checkExpr' cmp e t
        A.Pi _ tel e | null tel -> checkExpr' cmp e t
        A.Pi _ tel e -> do
            (t0, t') <- checkPiTelescope tel $ \ tel -> do
                    t0  <- instantiateFull =<< isType_ e
                    tel <- instantiateFull tel
                    return (t0, telePi tel t0)
            checkTelePiSort t'
            noFunctionsIntoSize t0 t'
            let s = getSort t'
                v = unEl t'
            when (s == Inf) $ reportSDoc "tc.term.sort" 20 $
              vcat [ text ("reduced to omega:")
                   , nest 2 $ "t   =" <+> prettyTCM t'
                   , nest 2 $ "cxt =" <+> (prettyTCM =<< getContextTelescope)
                   ]
            coerce cmp v (sort s) t

        A.Generalized s e -> do
            (_, t') <- generalizeType s $ isType_ e
            noFunctionsIntoSize t' t'
            let s = getSort t'
                v = unEl t'
            when (s == Inf) $ reportSDoc "tc.term.sort" 20 $
              vcat [ text ("reduced to omega:")
                   , nest 2 $ "t   =" <+> prettyTCM t'
                   , nest 2 $ "cxt =" <+> (prettyTCM =<< getContextTelescope)
                   ]
            coerce cmp v (sort s) t

        A.Fun _ (Arg info a) b -> do
            a' <- isType_ a
            b' <- isType_ b
            s  <- inferFunSort (getSort a') (getSort b')
            let v = Pi (defaultArgDom info a') (NoAbs underscore b')
            noFunctionsIntoSize b' $ El s v
            coerce cmp v (sort s) t
        A.Set _ n    -> do
          coerce cmp (Sort $ mkType n) (sort $ mkType $ n + 1) t
        A.Prop _ n   -> do
          unlessM isPropEnabled $ typeError NeedOptionProp
          coerce cmp (Sort $ mkProp n) (sort $ mkType $ n + 1) t

        A.Rec _ fs  -> checkRecordExpression cmp fs e t

        A.RecUpdate ei recexpr fs -> checkRecordUpdate cmp ei recexpr fs e t

        A.DontCare e -> -- resurrect vars
          ifM ((Irrelevant ==) <$> asksTC envRelevance)
            (dontCare <$> do applyRelevanceToContext Irrelevant $ checkExpr' cmp e t)
            (internalError "DontCare may only appear in irrelevant contexts")

        e0@(A.QuoteGoal _ x e) -> do
          qg <- quoteGoal t
          case qg of
            Left metas -> postponeTypeCheckingProblem (CheckExpr cmp e0 t) $ andM $ map isInstantiatedMeta metas
            Right quoted -> do
              tmType <- agdaTermType
              (v, ty) <- addLetBinding defaultArgInfo x quoted tmType (inferExpr e)
              coerce cmp v ty t
        e0@(A.QuoteContext _) -> do
          qc <- quoteContext
          case qc of
            Left metas -> postponeTypeCheckingProblem (CheckExpr cmp e0 t) $ andM $ map isInstantiatedMeta metas
            Right quotedContext -> do
              ctxType <- el $ list $ primArg <@> (unEl <$> agdaTypeType)
              coerce cmp quotedContext ctxType t
        e0@(A.Tactic i e xs ys) -> do
          qc <- quoteContext
          qg <- quoteGoal t
          let postpone metas = postponeTypeCheckingProblem (CheckExpr cmp e0 t) $ andM $ map isInstantiatedMeta metas
          case (qc, qg) of
            (Left metas1, Left metas2) -> postpone $ metas1 ++ metas2
            (Left metas , Right _    ) -> postpone $ metas
            (Right _    , Left metas ) -> postpone $ metas
            (Right quotedCtx, Right quotedGoal) -> do
              quotedCtx  <- defaultNamedArg <$> reify quotedCtx
              quotedGoal <- defaultNamedArg <$> reify quotedGoal
              let ai     = A.defaultAppInfo (getRange i)
                  tac    = foldl (A.App ai) (A.App ai (A.App ai e quotedCtx) quotedGoal) xs
                  result = foldl (A.App ai) (A.Unquote i) (defaultNamedArg tac : ys)
              checkExpr' cmp result t

        A.ETel _   -> __IMPOSSIBLE__

        A.Dot{} -> typeError $ GenericError $ "Invalid dotted expression"

        -- Application
        _   | Application hd args <- appView e -> checkApplication cmp hd args e t

      `catchIlltypedPatternBlockedOnMeta` \ (err, x) -> do
        -- We could not check the term because the type of some pattern is blocked.
        -- It has to be blocked on some meta, so we can postpone,
        -- being sure it will be retried when a meta is solved
        -- (which might be the blocking meta in which case we actually make progress).
        reportSDoc "tc.term" 50 $ vcat $
          [ "checking pattern got stuck on meta: " <+> text (show x) ]
        postponeTypeCheckingProblem (CheckExpr cmp e t) $ isInstantiatedMeta x

  where
  -- | Call checkExpr with an hidden lambda inserted if appropriate,
  --   else fallback.
  tryInsertHiddenLambda :: A.Expr -> Type -> TCM Term -> TCM Term
  tryInsertHiddenLambda e t fallback
    -- Insert hidden lambda if all of the following conditions are met:
        -- type is a hidden function type, {x : A} -> B or {{x : A}} -> B
    | Pi (Dom{domInfo = info, unDom = a}) b <- unEl t
        , let h = getHiding info
        , notVisible h
        -- expression is not a matching hidden lambda or question mark
        , not (hiddenLambdaOrHole h e)
        = do
      let proceed = doInsert info $ absName b
      -- If we skip the lambda insertion for an introduction,
      -- we will hit a dead end, so proceed no matter what.
      if definitelyIntroduction then proceed else do
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
      checkExpr' cmp (A.Lam (A.ExprRange re) (domainFree info x) e) t

    hiddenLambdaOrHole h e = case e of
      A.AbsurdLam _ h'        -> sameHiding h h'
      A.ExtendedLam _ _ _ cls -> any hiddenLHS cls
      A.Lam _ bind _          -> sameHiding h bind
      A.QuestionMark{}        -> True
      _                       -> False

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
      A.Set{}        -> True
      A.Prop{}       -> True
      A.Rec{}        -> True
      A.RecUpdate{}  -> True
      A.ScopedExpr{} -> __IMPOSSIBLE__
      A.ETel{}       -> __IMPOSSIBLE__
      _ -> False
---------------------------------------------------------------------------
-- * Reflection
---------------------------------------------------------------------------

doQuoteTerm :: Comparison -> Term -> Type -> TCM Term
doQuoteTerm cmp et t = do
  et'       <- etaContract =<< instantiateFull et
  let metas = allMetas et'
  case metas of
    _:_ -> postponeTypeCheckingProblem (DoQuoteTerm cmp et t) $ andM $ map isInstantiatedMeta metas
    []  -> do
      q  <- quoteTerm et'
      ty <- el primAgdaTerm
      coerce cmp q ty t

-- | Checking `quoteGoal` (deprecated)
quoteGoal :: Type -> TCM (Either [MetaId] Term)
quoteGoal t = do
  t' <- etaContract =<< instantiateFull t
  let metas = allMetas t'
  case metas of
    _:_ -> return $ Left metas
    []  -> do
      quotedGoal <- quoteTerm (unEl t')
      return $ Right quotedGoal

-- | Checking `quoteContext` (deprecated)
quoteContext :: TCM (Either [MetaId] Term)
quoteContext = do
  contextTypes  <- map (fmap snd) <$> getContext
  contextTypes  <- etaContract =<< instantiateFull contextTypes
  let metas = allMetas contextTypes
  case metas of
    _:_ -> return $ Left metas
    []  -> do
      quotedContext <- buildList <*> mapM quoteDom contextTypes
      return $ Right quotedContext

-- | Unquote a TCM computation in a given hole.
unquoteM :: A.Expr -> Term -> Type -> TCM ()
unquoteM tacA hole holeType = do
  tac <- checkExpr tacA =<< (el primAgdaTerm --> el (primAgdaTCM <#> primLevelZero <@> primUnit))
  inFreshModuleIfFreeParams $ unquoteTactic tac hole holeType

-- | Run a tactic `tac : Term → TC ⊤` in a hole (second argument) of the type
--   given by the third argument. Runs the continuation if successful.
unquoteTactic :: Term -> Term -> Type -> TCM ()
unquoteTactic tac hole goal = do
  ok  <- runUnquoteM $ unquoteTCM tac hole
  case ok of
    Left (BlockedOnMeta oldState x) -> do
      putTC oldState
      mi <- lookupMeta' x
      (r, meta) <- case mi of
        Nothing -> do -- fresh meta: need to block on something else!
          otherMetas <- allMetas <$> instantiateFull goal
          case otherMetas of
            []  -> return (noRange,     Nothing) -- Nothing to block on, leave it yellow. Alternative: fail.
            x:_ -> return (noRange,     Just x)  -- range?
        Just mi -> return (getRange mi, Just x)
      setCurrentRange r $
        addConstraint (UnquoteTactic meta tac hole goal)
    Left err -> typeError $ UnquoteFailed err
    Right _ -> return ()

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | Check an interaction point without arguments.
checkQuestionMark :: (Type -> TCM (MetaId, Term)) -> Type -> A.MetaInfo -> InteractionId -> TCM Term
checkQuestionMark new t0 i ii = do
  reportSDoc "tc.interaction" 20 $ sep
    [ "Found interaction point"
    , pretty ii
    , ":"
    , prettyTCM t0
    ]
  reportSDoc "tc.interaction" 60 $ sep
    [ "Raw:"
    , text (show t0)
    ]
  checkMeta (newQuestionMark' new ii) t0 i -- Andreas, 2013-05-22 use unreduced type t0!

-- | Check an underscore without arguments.
checkUnderscore :: Type -> A.MetaInfo -> TCM Term
checkUnderscore = checkMeta (newValueMeta RunMetaOccursCheck)

-- | Type check a meta variable.
checkMeta :: (Type -> TCM (MetaId, Term)) -> Type -> A.MetaInfo -> TCM Term
checkMeta newMeta t i = fst <$> checkOrInferMeta newMeta (Just t) i

-- | Infer the type of a meta variable.
--   If it is a new one, we create a new meta for its type.
inferMeta :: (Type -> TCM (MetaId, Term)) -> A.MetaInfo -> TCM (Elims -> Term, Type)
inferMeta newMeta i = mapFst applyE <$> checkOrInferMeta newMeta Nothing i

-- | Type check a meta variable.
--   If its type is not given, we return its type, or a fresh one, if it is a new meta.
--   If its type is given, we check that the meta has this type, and we return the same
--   type.
checkOrInferMeta :: (Type -> TCM (MetaId, Term)) -> Maybe Type -> A.MetaInfo -> TCM (Term, Type)
checkOrInferMeta newMeta mt i = do
  case A.metaNumber i of
    Nothing -> do
      setScope (A.metaScope i)
      t <- maybe (workOnTypes $ newTypeMeta_) return mt
      (x, v) <- newMeta t
      setMetaNameSuggestion x (A.metaNameSuggestion i)
      return (v, t)
    -- Rechecking an existing metavariable
    Just x -> do
      let v = MetaV x []
      reportSDoc "tc.meta.check" 20 $
        "checking existing meta " <+> prettyTCM v
      t' <- jMetaType . mvJudgement <$> lookupMeta x
      reportSDoc "tc.meta.check" 20 $
        nest 2 $ "of type " <+> prettyTCM t'
      case mt of
        Nothing -> return (v, t')
        Just t  -> (,t) <$> coerce CmpLeq v t' t

-- | Turn a domain-free binding (e.g. lambda) into a domain-full one,
--   by inserting an underscore for the missing type.
domainFree :: ArgInfo -> A.Name -> A.LamBinding
domainFree info x =
  A.DomainFull $ A.TBind r [unnamedArg info $ A.BindName x] $ A.Underscore underscoreInfo
  where
    r = getRange x
    underscoreInfo = A.MetaInfo
      { A.metaRange          = r
      , A.metaScope          = emptyScopeInfo
      , A.metaNumber         = Nothing
      , A.metaNameSuggestion = prettyShow $ A.nameConcrete x
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
  (vs', t') <- traceCall (SetRange $ getRange arg) $ checkKnownArgument arg vs t
  checkKnownArguments args vs' t'

-- | Check an argument whose value we already know.

checkKnownArgument
  :: NamedArg A.Expr    -- ^ User-supplied argument.
  -> Args               -- ^ Inferred arguments (including hidden ones).
  -> Type               -- ^ Type of the head (must be Pi-type with enough domains).
  -> TCM (Args, Type)   -- ^ Remaining inferred arguments, remaining type.
checkKnownArgument arg [] _ = genericDocError =<< do
  "Invalid projection parameter " <+> prettyA arg
checkKnownArgument arg@(Arg info e) (Arg _infov v : vs) t = do
  (Dom{domInfo = info',unDom = a}, b) <- mustBePi t
  -- Skip the arguments from vs that do not correspond to e
  if not (sameHiding info info'
          && (visible info || maybe True ((absName b ==) . rangedThing) (nameOf e)))
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
  let x = maybe "" rangedThing $ nameOf e0
  traceCall (CheckExprCall CmpLeq e t0) $ do
    reportSDoc "tc.term.args.named" 15 $ do
        "Checking named arg" <+> sep
          [ fsep [ prettyTCM arg, ":", prettyTCM t0 ]
          ]
    reportSLn "tc.term.args.named" 75 $ "  arg = " ++ show (deepUnscope arg)
    -- Ulf, 2017-03-24: (#2172) Always treat explicit _ and ? as implicit
    -- argument (i.e. solve with unification).
    let checkU = checkMeta (newMetaArg (setHiding Hidden info) x) t0
    let checkQ = checkQuestionMark (newInteractionMetaArg (setHiding Hidden info) x) t0
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
defOrVar A.Def{} = True
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
inferExprForWith :: A.Expr -> TCM (Term, Type)
inferExprForWith e = do
  reportSDoc "tc.with.infer" 20 $ "inferExprforWith " <+> prettyTCM e
  reportSLn  "tc.with.infer" 80 $ "inferExprforWith " ++ show (deepUnscope e)
  traceCall (InferExpr e) $ do
    -- With wants type and term fully instantiated!
    (v, t) <- instantiateFull =<< inferExpr e
    v0 <- reduce v
    -- Andreas 2014-11-06, issue 1342.
    -- Check that we do not `with` on a module parameter!
    case v0 of
      Var i [] -> whenM (isModuleFreeVar i) $ do
        reportSDoc "tc.with.infer" 80 $ vcat
          [ text $ "with expression is variable " ++ show i
          , "current modules = " <+> do text . show =<< currentModule
          , "current module free vars = " <+> do text . show =<< getCurrentModuleFreeVars
          , "context size = " <+> do text . show =<< getContextSize
          , "current context = " <+> do prettyTCM =<< getContextTelescope
          ]
        typeError $ WithOnFreeVariable e v0
      _        -> return ()
    -- Possibly insert hidden arguments.
    TelV tel t0 <- telViewUpTo' (-1) (not . visible) t
    case unEl t0 of
      Def d vs -> do
        res <- isDataOrRecordType d
        case res of
          Nothing -> return (v, t)
          Just{}  -> do
            (args, t1) <- implicitArgs (-1) notVisible t
            return (v `apply` args, t1)
      _ -> return (v, t)

---------------------------------------------------------------------------
-- * Let bindings
---------------------------------------------------------------------------

checkLetBindings :: [A.LetBinding] -> TCM a -> TCM a
checkLetBindings = foldr (.) id . map checkLetBinding

checkLetBinding :: A.LetBinding -> TCM a -> TCM a

checkLetBinding b@(A.LetBind i info x t e) ret =
  traceCall (CheckLetBinding b) $ do
    t <- isType_ t
    v <- applyModalityToContext info $ checkDontExpandLast CmpLeq e t
    addLetBinding info (A.unBind x) v t ret

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
        , "cxtRel=" <+> do pretty =<< asksTC envRelevance
        ]
      ]
    fvs <- getContextSize
    checkLeftHandSide (CheckPattern p EmptyTel t) Nothing [p0] t0 Nothing [] $ \ (LHSResult _ delta0 ps _ _t _ asb _) -> bindAsPatterns asb $ do
          -- After dropping the free variable patterns there should be a single pattern left.
      let p = case drop fvs ps of [p] -> namedArg p; _ -> __IMPOSSIBLE__
          -- Also strip the context variables from the telescope
          delta = telFromList $ drop fvs $ telToList delta0
      reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
        [ "p (I) =" <+> prettyTCM p
        , "delta =" <+> prettyTCM delta
        , "cxtRel=" <+> do pretty =<< asksTC envRelevance
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
        foldr (uncurry4 addLetBinding) ret $ List.zip4 infos xs sigma ts

checkLetBinding (A.LetApply i x modapp copyInfo _adir) ret = do
  -- Any variables in the context that doesn't belong to the current
  -- module should go with the new module.
  -- Example: @f x y = let open M t in u@.
  -- There are 2 @new@ variables, @x@ and @y@, going into the anonynous module
  -- @module _ (x : _) (y : _) = M t@.
  fv   <- getCurrentModuleFreeVars
  n    <- getContextSize
  let new = n - fv
  reportSLn "tc.term.let.apply" 10 $ "Applying " ++ show modapp ++ " with " ++ show new ++ " free variables"
  reportSDoc "tc.term.let.apply" 20 $ vcat
    [ "context =" <+> (prettyTCM =<< getContextTelescope)
    , "module  =" <+> (prettyTCM =<< currentModule)
    , "fv      =" <+> (text $ show fv)
    ]
  checkSectionApplication i x modapp copyInfo
  withAnonymousModule x new ret
-- LetOpen and LetDeclaredVariable are only used for highlighting.
checkLetBinding A.LetOpen{} ret = ret
checkLetBinding (A.LetDeclaredVariable _) ret = ret
