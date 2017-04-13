{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Term where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Arrow ((&&&), (***), first, second)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.State (get, put)
import Control.Monad.Reader

import Data.Maybe
import Data.Either (partitionEithers)
import Data.Monoid (mappend)
import Data.List hiding (sort, null)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (sequenceA)
import Data.Void

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Generate (storeDisambiguatedName)

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Concrete.Pretty () -- only Pretty instances
import Agda.Syntax.Concrete (FieldAssignment'(..), nameFieldA, exprFieldA)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.Syntax.Literal
import qualified Agda.Syntax.Reflected as R
import Agda.Syntax.Scope.Base ( ThingsInScope, AbstractName
                              , emptyScopeInfo
                              , exportedNamesInScope)
import Agda.Syntax.Scope.Monad (getNamedScope)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.Syntax.Translation.ReflectedToAbstract (toAbstract_)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free (isBinderUsed)
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Quote
import Agda.TypeChecking.Unquote
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.SizedTypes.Solve
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rules.LHS

import {-# SOURCE #-} Agda.TypeChecking.Empty (isEmptyType)
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl (checkSectionApplication)
import {-# SOURCE #-} Agda.TypeChecking.Rules.Def (checkFunDef, checkFunDef', useTerPragma)

import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List (groupOn)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
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
isType_ e =
  traceCall (IsType_ e) $ sharedType =<< do
  let fallback = isType e =<< do workOnTypes $ newSortMeta
  case unScope e of
    A.Fun i (Arg info t) b -> do
      a <- Dom info <$> isType_ t
      b <- isType_ b
      s <- ptsRule a b
      let t' = El s $ Pi a $ NoAbs underscore b
      noFunctionsIntoSize b t'
      return t'
    A.Pi _ tel e | null tel -> isType_ e
    A.Pi _ tel e -> do
      (t0, t') <- checkPiTelescope tel $ \ tel -> do
        t0  <- instantiateFull =<< isType_ e
        tel <- instantiateFull tel
        return (t0, telePi tel t0)
      noFunctionsIntoSize t0 t'
      return t'
    A.Set _ n    -> do
      return $ sort (mkType n)
    A.App i s arg
      | getHiding arg == NotHidden,
        A.Set _ 0 <- unScope s ->
      ifNotM hasUniversePolymorphism
          (typeError $ GenericError "Use --universe-polymorphism to enable level arguments to Set")
      $ {- else -} do
        lvl <- levelType
        -- allow NonStrict variables when checking level
        --   Set : (NonStrict) Level -> Set\omega
        n   <- levelView =<< do
          applyRelevanceToContext NonStrict $
            checkNamedArg arg lvl
        return $ sort (Type n)

    -- Issue #707: Check an existing interaction point
    A.QuestionMark minfo ii -> caseMaybeM (lookupInteractionMeta ii) fallback $ \ x -> do
      -- -- | Just x <- A.metaNumber minfo -> do
      reportSDoc "tc.ip" 20 $ fsep
        [ text "Rechecking meta "
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
        [ text "  s0   = " <+> prettyTCM s0
        , text "  vs   = " <+> prettyTCM vs
        , text "  rest = " <+> prettyTCM rest
        ]
      -- We assume the meta variable use here is in an extension of the original context.
      -- If not we revert to the old buggy behavior of #707 (see test/Succeed/Issue2257b).
      if (length vs /= n) then fallback else do
      s1  <- piApplyM s0 vs
      case ignoreSharing $ unEl s1 of
        Sort s -> return $ El s $ MetaV x $ map Apply vs
        _ -> __IMPOSSIBLE__

    _ -> fallback

ptsRule :: (LensSort a, LensSort b) => a -> b -> TCM Sort
ptsRule a b = pts <$> reduce (getSort a) <*> reduce (getSort b)

-- | Ensure that a (freshly created) function type does not inhabit 'SizeUniv'.
--   Precondition:  When @noFunctionsIntoSize t tBlame@ is called,
--   we are in the context of @tBlame@ in order to print it correctly.
--   Not being in context of @t@ should not matter, as we are only
--   checking whether its sort reduces to 'SizeUniv'.
noFunctionsIntoSize :: Type -> Type -> TCM ()
noFunctionsIntoSize t tBlame = do
  reportSDoc "tc.fun" 20 $ do
    let El s (Pi dom b) = ignoreSharing <$> tBlame
    sep [ text "created function type " <+> prettyTCM tBlame
        , text "with pts rule" <+> prettyTCM (getSort dom, getSort b, s)
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

{- UNUSED
-- | Force a type to be a Pi. Instantiates if necessary. The 'Hiding' is only
--   used when instantiating a meta variable.

forcePi :: Hiding -> String -> Type -> TCM Type
forcePi h name (El s t) =
    do  t' <- reduce t
        case t' of
            Pi _ _      -> return $ El s t'
            _           -> do
                sa <- newSortMeta
                sb <- newSortMeta
                let s' = sLub sa sb

                a <- newTypeMeta sa
                x <- freshName_ name
                let arg = setHiding h $ defaultDom a
                b <- addContext (x, arg) $ newTypeMeta sb
                let ty = El s' $ Pi arg (Abs (show x) b)
                equalType (El s t') ty
                ty' <- reduce ty
                return ty'
-}

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

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
checkTypedBindings :: LamOrPi -> A.TypedBindings -> (Telescope -> TCM a) -> TCM a
checkTypedBindings lamOrPi (A.TypedBindings i (Arg info b)) ret =
    checkTypedBinding lamOrPi info b $ \ bs ->
    ret $ telFromList bs

checkTypedBinding :: LamOrPi -> ArgInfo -> A.TypedBinding -> (ListTel -> TCM a) -> TCM a
checkTypedBinding lamOrPi info (A.TBind i xs e) ret = do
    -- Andreas, 2011-04-26 irrelevant function arguments may appear
    -- non-strictly in the codomain type
    -- 2011-10-04 if flag --experimental-irrelevance is set
    experimental <- optExperimentalIrrelevance <$> pragmaOptions
    t <- modEnv lamOrPi $ isType_ e
    let info' = mapRelevance (modRel lamOrPi experimental) info
    addContext' (xs, Dom info' t) $
      ret $ bindsWithHidingToTel xs (Dom info t)
    where
        -- if we are checking a typed lambda, we resurrect before we check the
        -- types, but do not modify the new context entries
        -- otherwise, if we are checking a pi, we do not resurrect, but
        -- modify the new context entries
        modEnv LamNotPi = workOnTypes
        modEnv _        = id
        modRel PiNotLam xp = if xp then irrToNonStrict else nonStrictToRel
        modRel _        _  = id
checkTypedBinding lamOrPi info (A.TLet _ lbs) ret = do
    checkLetBindings lbs (ret [])

---------------------------------------------------------------------------
-- * Lambda abstractions
---------------------------------------------------------------------------

-- | Type check a lambda expression.
checkLambda :: Arg A.TypedBinding -> A.Expr -> Type -> TCM Term
checkLambda (Arg _ (A.TLet _ lbs)) body target =
  checkLetBindings lbs (checkExpr body target)
checkLambda (Arg info (A.TBind _ xs typ)) body target = do
  reportSLn "tc.term.lambda" 60 $ "checkLambda   xs = " ++ show xs

  let numbinds = length xs
  TelV tel btyp <- telViewUpTo numbinds target
  if size tel < numbinds || numbinds /= 1
    then dontUseTargetType
    else useTargetType tel btyp
  where
    dontUseTargetType = do
      -- Checking λ (xs : argsT) → body : target
      verboseS "tc.term.lambda" 5 $ tick "lambda-no-target-type"

      -- First check that argsT is a valid type
      argsT <- workOnTypes $ Dom info <$> isType_ typ
      -- Andreas, 2015-05-28 Issue 1523
      -- If argsT is a SizeLt, it must be non-empty to avoid non-termination.
      -- TODO: do we need to block checkExpr?
      checkSizeLtSat $ unEl $ unDom argsT

      -- In order to have as much type information as possible when checking
      -- body, we first unify (xs : argsT) → ?t₁ with the target type. If this
      -- is inconclusive we need to block the resulting term so we create a
      -- fresh problem for the check.
      let tel = telFromList $ bindsWithHidingToTel xs argsT
      reportSLn "tc.term.lambda" 60 $ "dontUseTargetType tel = " ++ show tel
      -- DONT USE tel for addContext, as it loses NameIds.
      -- WRONG: t1 <- addContext tel $ workOnTypes newTypeMeta_
      t1 <- addContext (xs, argsT) $ workOnTypes newTypeMeta_
      -- Do not coerce hidden lambdas
      if notVisible info || any notVisible xs then do
        pid <- newProblem_ $ leqType (telePi tel t1) target
        -- Now check body : ?t₁
        -- WRONG: v <- addContext tel $ checkExpr body t1
        v <- addContext' (xs, argsT) $ checkExpr body t1
        -- Block on the type comparison
        blockTermOnProblem target (teleLam tel v) pid
       else do
        -- Now check body : ?t₁
        -- WRONG: v <- addContext tel $ checkExpr body t1
        v <- addContext' (xs, argsT) $ checkExpr body t1
        -- Block on the type comparison
        coerce (teleLam tel v) (telePi tel t1) target

    useTargetType tel@(ExtendTel dom (Abs y EmptyTel)) btyp = do
        verboseS "tc.term.lambda" 5 $ tick "lambda-with-target-type"
        reportSLn "tc.term.lambda" 60 $ "useTargetType y  = " ++ show y

        -- merge in the hiding info of the TBind
        let [WithHiding h x] = xs
        info <- return $ mapHiding (mappend h) info
        unless (getHiding dom == getHiding info) $ typeError $ WrongHidingInLambda target
        -- Andreas, 2011-10-01 ignore relevance in lambda if not explicitly given
        info <- lambdaIrrelevanceCheck info dom
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
        v <- lambdaAddContext x y (Dom info argT) $ checkExpr body btyp
        blockTermOnProblem target (Lam info $ Abs (nameToArgName x) v) pid

    useTargetType _ _ = __IMPOSSIBLE__

-- | Check that irrelevance info in lambda is compatible with irrelevance
--   coming from the function type.
--   If lambda has no user-given relevance, copy that of function type.
lambdaIrrelevanceCheck :: LensRelevance dom => ArgInfo -> dom -> TCM ArgInfo
lambdaIrrelevanceCheck info dom
    -- Case: no specific user annotation: use relevance of function type
  | isRelevant info = return $ setRelevance (getRelevance dom) info
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

lambdaAddContext :: Name -> ArgName -> Dom Type -> TCM a -> TCM a
lambdaAddContext x y dom
  | isNoName x = addContext' (notInScopeName y, dom)  -- Note: String instance
  | otherwise  = addContext' (x, dom)                 -- Name instance of addContext'

-- | Checking a lambda whose domain type has already been checked.
checkPostponedLambda :: Arg ([WithHiding Name], Maybe Type) -> A.Expr -> Type -> TCM Term
checkPostponedLambda args@(Arg _    ([]    , _ )) body target = do
  checkExpr body target
checkPostponedLambda args@(Arg info (WithHiding h x : xs, mt)) body target = do
  let postpone _ t = postponeTypeCheckingProblem_ $ CheckLambda args body t
      lamHiding = mappend h $ getHiding info
  insertHiddenLambdas lamHiding target postpone $ \ t@(El _ (Pi dom b)) -> do
    -- Andreas, 2011-10-01 ignore relevance in lambda if not explicitly given
    info' <- setHiding lamHiding <$> lambdaIrrelevanceCheck info dom
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
      checkPostponedLambda (Arg info (xs, mt)) body $ absBody b
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
  ifBlockedType target postpone $ \ t0 -> do
    let t = ignoreSharing <$> t0
    case unEl t of

      Pi dom b -> do
        let h' = getHiding dom
        -- Found expected hiding: return function type.
        if h == h' then ret t else do
          -- Found a visible argument but expected a hidden one:
          -- That's an error, as we cannot insert a visible lambda.
          if visible h' then typeError $ WrongHidingInLambda target else do
            -- Otherwise, we found a hidden argument that we can insert.
            let x = absName b
            Lam (domInfo dom) . Abs x <$> do
              addContext' (x, dom) $ insertHiddenLambdas h (absBody b) postpone ret

      _ -> typeError . GenericDocError =<< do
        text "Expected " <+> prettyTCM target <+> text " to be a function type"

-- | @checkAbsurdLambda i h e t@ checks absurd lambda against type @t@.
--   Precondition: @e = AbsurdLam i h@
checkAbsurdLambda :: A.ExprInfo -> Hiding -> A.Expr -> Type -> TCM Term
checkAbsurdLambda i h e t = do
  t <- instantiateFull t
  ifBlockedType t (\ m t' -> postponeTypeCheckingProblem_ $ CheckExpr e t') $ \ t' -> do
    case ignoreSharing $ unEl t' of
      Pi dom@(Dom info' a) b
        | h /= getHiding info' -> typeError $ WrongHidingInLambda t'
        | not (null $ allMetas a) ->
            postponeTypeCheckingProblem (CheckExpr e t') $
              null . allMetas <$> instantiateFull a
        | otherwise -> blockTerm t' $ do
          isEmptyType (getRange i) a
          -- Add helper function
          top <- currentModule
          aux <- qualify top <$> freshName_ (getRange i, absurdLambdaName)
          -- if we are in irrelevant position, the helper function
          -- is added as irrelevant
          rel <- asks envRelevance
          reportSDoc "tc.term.absurd" 10 $ vcat
            [ text "Adding absurd function" <+> prettyTCM rel <> prettyTCM aux
            , nest 2 $ text "of type" <+> prettyTCM t'
            ]
          addConstant aux $
            (\ d -> (defaultDefn (setRelevance rel info') aux t' d)
                    { defPolarity       = [Nonvariant]
                    , defArgOccurrences = [Unused] })
            $ emptyFunction
              { funClauses        =
                  [Clause
                    { clauseLHSRange  = getRange e
                    , clauseFullRange = getRange e
                    , clauseTel       = telFromList [fmap ("()",) dom]
                    , namedClausePats = [Arg info' $ Named (Just $ unranged $ absName b) $ debruijnNamedVar "()" 0]
                    , clauseBody      = Nothing
                    , clauseType      = Just $ setRelevance rel $ defaultArg $ absBody b
                    , clauseCatchall  = False
                    }
                  ]
              , funCompiled       = Just Fail
              , funTerminates     = Just True
              }
          -- Andreas 2012-01-30: since aux is lifted to toplevel
          -- it needs to be applied to the current telescope (issue 557)
          tel <- getContextTelescope
          return $ Def aux $ map Apply $ teleArgs tel
      _ -> typeError $ ShouldBePi t'

-- | @checkExtendedLambda i di qname cs e t@ check pattern matching lambda.
-- Precondition: @e = ExtendedLam i di qname cs@
checkExtendedLambda :: A.ExprInfo -> A.DefInfo -> QName -> [A.Clause] ->
                       A.Expr -> Type -> TCM Term
checkExtendedLambda i di qname cs e t = do
   -- Andreas, 2016-06-16 issue #2045
   -- Try to get rid of unsolved size metas before we
   -- fix the type of the extended lambda auxiliary function
   solveSizeConstraints DontDefaultToInfty
   t <- instantiateFull t
   ifBlockedType t (\ m t' -> postponeTypeCheckingProblem_ $ CheckExpr e t') $ \ t -> do
     j   <- currentOrFreshMutualBlock
     rel <- asks envRelevance
     let info = setRelevance rel defaultArgInfo
     -- Andreas, 2016-07-13, issue 2028.
     -- Save the state to rollback the changes to the signature.
     st <- get
     -- Andreas, 2013-12-28: add extendedlambda as @Function@, not as @Axiom@;
     -- otherwise, @addClause@ in @checkFunDef'@ fails (see issue 1009).
     addConstant qname =<< do
       useTerPragma $
         (defaultDefn info qname t emptyFunction) { defMutual = j }
     reportSDoc "tc.term.exlam" 20 $
       text (show $ A.defAbstract di) <+>
       text "extended lambda's implementation \"" <> prettyTCM qname <>
       text "\" has type: " $$ prettyTCM t -- <+> text " where clauses: " <+> text (show cs)
     args     <- getContextArgs
     freevars <- getCurrentModuleFreeVars
     let argsNoParam = genericDrop freevars args -- don't count module parameters
     let (hid, notHid) = partition notVisible argsNoParam
     reportSDoc "tc.term.exlam" 30 $ vcat $
       [ text "dropped args: " <+> prettyTCM (take freevars args)
       , text "hidden  args: " <+> prettyTCM hid
       , text "visible args: " <+> prettyTCM notHid
       ]
     -- Andreas, Ulf, 2016-02-02: We want to postpone type checking an extended lambda
     -- in case the lhs checker failed due to insufficient type info for the patterns.
     -- Issues 480, 1159, 1811.
     mx <- catchIlltypedPatternBlockedOnMeta $ abstract (A.defAbstract di) $
       checkFunDef' t info NotDelayed (Just $ ExtLamInfo (length hid) (length notHid)) Nothing di qname cs
     case mx of
       -- Case: type checking succeeded, so we go ahead.
       Nothing -> return $ Def qname $ map Apply args
       -- Case: we could not check the extended lambda because we are blocked on a meta.
       -- In this case, we want to postpone.
       Just (err, x) -> do
         -- Note that we messed up the state a bit.  We might want to unroll these state changes.
         -- However, they are mostly harmless:
         -- 1. We created a new mutual block id.
         -- 2. We added a constant without definition.

         -- In fact, they are not so harmless, see issue 2028!
         -- Thus, reset the state!
         put st

         -- The meta might not be known in the reset state, as it could have been created
         -- somewhere on the way to the type error.
         mm <- Map.lookup x <$> getMetaStore
         case mvInstantiation <$> mm of
           -- Case: we do not know the meta
           Nothing -> do
             -- TODO: mine for a meta in t
             -- For now, we fail.
             throwError err
           -- Case: we know the meta here.
           Just InstV{} -> __IMPOSSIBLE__  -- It cannot be instantiated yet.
           Just{} -> do
             -- It has to be blocked on some meta, so we can postpone,
             -- being sure it will be retired when a meta is solved
             -- (which might be the blocking meta in which case we actually make progress).
             postponeTypeCheckingProblem (CheckExpr e t) $ isInstantiatedMeta x
  where
    -- Concrete definitions cannot use information about abstract things.
    abstract ConcreteDef = inConcreteMode
    abstract AbstractDef = inAbstractMode

-- | Run a computation.
--
--   * If successful, return Nothing.
--
--   * If @IlltypedPattern p a@ is thrown and type @a@ is blocked on some meta @x@
--     return @Just x@.  Note that the returned meta might only exists in the state
--     where the error was thrown, thus, be an invalid 'MetaId' in the current state.
--
--   * If another error was thrown or the type @a@ is not blocked, reraise the error.
--
catchIlltypedPatternBlockedOnMeta :: TCM () -> TCM (Maybe (TCErr, MetaId))
catchIlltypedPatternBlockedOnMeta m = (Nothing <$ do disableDestructiveUpdate m)
  `catchError` \ err -> do
  let reraise = throwError err
  case err of
    TypeError s cl@Closure{ clValue = IlltypedPattern p a } -> do
      mx <- localState $ do
        put s
        enterClosure cl $ \ _ -> do
          ifBlockedType a (\ x _ -> return $ Just x) $ {- else -} \ _ -> return Nothing
      caseMaybe mx reraise $ \ x -> return $ Just (err, x)
    _ -> reraise

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

expandModuleAssigns :: [Either A.Assign A.ModuleName] -> [C.Name] -> TCM A.Assigns
expandModuleAssigns mfs exs = do
  let (fs , ms) = partitionEithers mfs
      exs' = exs \\ map (view nameFieldA) fs
  fs' <- forM exs' $ \ f -> do
    pms <- forM ms $ \ m -> do
       modScope <- getNamedScope m
       let names :: ThingsInScope AbstractName
           names = exportedNamesInScope modScope
       return $
        case Map.lookup f names of
          Just [n] -> Just (m, FieldAssignment f (A.nameExpr n))
          _        -> Nothing

    case catMaybes pms of
      []        -> return Nothing
      [(_, fa)] -> return (Just fa)
      mfas      -> typeError $ GenericError $ "Ambiguity: the field " ++ show f ++ " appears in the following modules " ++ show (map fst mfas)
  return (fs ++ catMaybes fs')

-- | @checkRecordExpression fs e t@ checks record construction against type @t@.
-- Precondition @e = Rec _ fs@.
checkRecordExpression :: A.RecordAssigns  -> A.Expr -> Type -> TCM Term
checkRecordExpression mfs e t = do
  reportSDoc "tc.term.rec" 10 $ sep
    [ text "checking record expression"
    , prettyA e
    ]
  ifBlockedType t (\ _ t -> guessRecordType t) {-else-} $ \ t -> do
  case ignoreSharing $ unEl t of
    -- Case: We know the type of the record already.
    Def r es  -> do
      let ~(Just vs) = allApplyElims es
      reportSDoc "tc.term.rec" 20 $ text $ "  r   = " ++ show r

      reportSDoc "tc.term.rec" 30 $ text "  xs  = " <> do
        text =<< show . map unArg <$> getRecordFieldNames r
      reportSDoc "tc.term.rec" 30 $ text "  ftel= " <> do
        prettyTCM =<< getRecordFieldTypes r
      reportSDoc "tc.term.rec" 30 $ text "  con = " <> do
        text =<< show <$> getRecordConstructor r

      def <- getRecordDef r
      let -- Field names with ArgInfo.
          axs  = recordFieldNames def
          exs  = filter visible axs
          -- Just field names.
          xs   = map unArg axs
          -- Record constructor.
          con  = killRange $ recConHead def
      reportSDoc "tc.term.rec" 20 $ vcat
        [ text $ "  xs  = " ++ show xs
        , text   "  ftel= " <> prettyTCM (recTel def)
        , text $ "  con = " ++ show con
        ]

      -- Compute the list of given fields, decorated with the ArgInfo from the record def.
      fs <- expandModuleAssigns mfs (map unArg exs)

      -- Compute a list of metas for the missing visible fields.
      scope <- getScope
      let re = getRange e
          meta x = A.Underscore $ A.MetaInfo re scope Nothing (show x)
      -- In @es@ omitted explicit fields are replaced by underscores.
      -- Omitted implicit or instance fields
      -- are still left out and inserted later by checkArguments_.
      es <- insertMissingFields r meta fs axs

      args <- checkArguments_ ExpandLast re es (recTel def `apply` vs) >>= \case
        (args, remainingTel) | null remainingTel -> return args
        _ -> __IMPOSSIBLE__
      -- Don't need to block here!
      reportSDoc "tc.term.rec" 20 $ text $ "finished record expression"
      return $ Con con ConORec args
    _         -> typeError $ ShouldBeRecordType t

  where
    guessRecordType t = do
      let fields = [ x | Left (FieldAssignment x _) <- mfs ]
      rs <- findPossibleRecords fields
      case rs of
          -- If there are no records with the right fields we might as well fail right away.
        [] -> case fields of
          []  -> typeError $ GenericError "There are no records in scope"
          [f] -> typeError $ GenericError $ "There is no known record with the field " ++ show f
          _   -> typeError $ GenericError $ "There is no known record with the fields " ++ unwords (map show fields)
          -- If there's only one record with the appropriate fields, go with that.
        [r] -> do
          def <- getConstInfo r
          let rt = defType def
          vs  <- newArgsMeta rt
          target <- reduce $ piApply rt vs
          s  <- case ignoreSharing $ unEl target of
                  Level l -> return $ Type l
                  Sort s  -> return s
                  v       -> do
                    reportSDoc "impossible" 10 $ vcat
                      [ text "The impossible happened when checking record expression against meta"
                      , text "Candidate record type r = " <+> prettyTCM r
                      , text "Type of r               = " <+> prettyTCM rt
                      , text "Ends in (should be sort)= " <+> prettyTCM v
                      , text $ "  Raw                   =  " ++ show v
                      ]
                    __IMPOSSIBLE__
          let inferred = El s $ Def r $ map Apply vs
          v <- checkExpr e inferred
          coerce v inferred t
          -- Andreas 2012-04-21: OLD CODE, WRONG DIRECTION, I GUESS:
          -- blockTerm t $ v <$ leqType_ t inferred

          -- If there are more than one possible record we postpone
        _:_:_ -> do
          reportSDoc "tc.term.expr.rec" 10 $ sep
            [ text "Postponing type checking of"
            , nest 2 $ prettyA e <+> text ":" <+> prettyTCM t
            ]
          postponeTypeCheckingProblem_ $ CheckExpr e t


-- | @checkRecordUpdate ei recexpr fs e t@
-- Precondition @e = RecUpdate ei recexpr fs@.
checkRecordUpdate :: A.ExprInfo -> A.Expr -> A.Assigns -> A.Expr -> Type -> TCM Term
checkRecordUpdate ei recexpr fs e t = do
  case ignoreSharing $ unEl t of
    Def r vs  -> do
      v <- checkExpr recexpr t
      name <- freshNoName (getRange recexpr)
      addLetBinding defaultArgInfo name v t $ do
        projs <- recFields <$> getRecordDef r
        axs <- getRecordFieldNames r
        scope <- getScope
        let xs = map unArg axs
        es <- orderFields r Nothing xs $ map (\ (FieldAssignment x e) -> (x, Just e)) fs
        let es' = zipWith (replaceFields name ei) projs es
        checkExpr (A.Rec ei [ Left (FieldAssignment x e) | (x, Just e) <- zip xs es' ]) t
    MetaV _ _ -> do
      inferred <- inferExpr recexpr >>= reduce . snd
      case ignoreSharing $ unEl inferred of
        MetaV _ _ -> postponeTypeCheckingProblem_ $ CheckExpr e t
        _         -> do
          v <- checkExpr e inferred
          coerce v inferred t
    _         -> typeError $ ShouldBeRecordType t
  where
    replaceFields :: Name -> A.ExprInfo -> Arg A.QName -> Maybe A.Expr -> Maybe A.Expr
    replaceFields n ei a@(Arg _ p) Nothing | visible a =
        Just $ A.App ei (A.Def p) $ defaultNamedArg $ A.Var n
    replaceFields _ _  (Arg _ _) Nothing  = Nothing
    replaceFields _ _  _         (Just e) = Just $ e

---------------------------------------------------------------------------
-- * Literal
---------------------------------------------------------------------------

checkLiteral :: Literal -> Type -> TCM Term
checkLiteral lit t = do
  t' <- litType lit
  coerce (Lit lit) t' t

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | @checkArguments' exph r args t0 t k@ tries @checkArguments exph args t0 t@.
-- If it succeeds, it continues @k@ with the returned results.  If it fails,
-- it registers a postponed typechecking problem and returns the resulting new
-- meta variable.
--
-- Checks @e := ((_ : t0) args) : t@.
checkArguments' ::
  ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
  (Args -> Type -> TCM Term) -> TCM Term
checkArguments' exph r args t0 t k = do
  z <- runExceptT $ checkArguments exph r args t0 t
  case z of
    Right (vs, t1) -> k vs t1
      -- vs = evaluated args
      -- t1 = remaining type (needs to be subtype of t)
    Left (us, es, t0) -> do
      reportSDoc "tc.term.expr.args" 80 $
        sep [ text "postponed checking arguments"
            , nest 4 $ prettyList (map (prettyA . namedThing . unArg) args)
            , nest 2 $ text "against"
            , nest 4 $ prettyTCM t0 ] $$
        sep [ text "progress:"
            , nest 2 $ text "checked" <+> prettyList (map prettyTCM us)
            , nest 2 $ text "remaining" <+> sep [ prettyList (map (prettyA . namedThing . unArg) es)
                                                , nest 2 $ text ":" <+> prettyTCM t0 ] ]
      postponeTypeCheckingProblem_ (CheckArgs exph r es t0 t $ \vs t -> k (us ++ vs) t)
      -- if unsuccessful, postpone checking until t0 unblocks


-- | Remove top layers of scope info of expression and set the scope accordingly
--   in the 'TCState'.

scopedExpr :: A.Expr -> TCM A.Expr
scopedExpr (A.ScopedExpr scope e) = setScope scope >> scopedExpr e
scopedExpr e                      = return e

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t0 =
  verboseBracket "tc.term.expr.top" 5 "checkExpr" $
  traceCall (CheckExprCall e t0) $ localScope $ doExpandLast $ shared =<< do
    reportSDoc "tc.term.expr.top" 15 $
        text "Checking" <+> sep
          [ fsep [ prettyTCM e, text ":", prettyTCM t0 ]
          , nest 2 $ text "at " <+> (text . show =<< getCurrentRange)
          ]
    reportSDoc "tc.term.expr.top.detailed" 80 $
      text "Checking" <+> fsep [ prettyTCM e, text ":", text (show t0) ]
    t <- reduce t0
    reportSDoc "tc.term.expr.top" 15 $
        text "    --> " <+> prettyTCM t

    e <- scopedExpr e

    tryInsertHiddenLambda e t $ case e of

        A.ScopedExpr scope e -> __IMPOSSIBLE__ -- setScope scope >> checkExpr e t

        -- a meta variable without arguments: type check directly for efficiency
        A.QuestionMark i ii -> checkQuestionMark (newValueMeta' DontRunMetaOccursCheck) t0 i ii
        A.Underscore i -> checkUnderscore t0 i

        A.WithApp _ e es -> typeError $ NotImplemented "type checking of with application"

        -- check |- Set l : t  (requires universe polymorphism)
        A.App i s arg@(Arg ai l)
          | A.Set _ 0 <- unScope s, visible ai ->
          ifNotM hasUniversePolymorphism
              (typeError $ GenericError "Use --universe-polymorphism to enable level arguments to Set")
          $ {- else -} do
            lvl <- levelType
            -- allow NonStrict variables when checking level
            --   Set : (NonStrict) Level -> Set\omega
            n   <- levelView =<< do
              applyRelevanceToContext NonStrict $
                checkNamedArg arg lvl
            -- check that Set (l+1) <= t
            reportSDoc "tc.univ.poly" 10 $
              text "checking Set " <+> prettyTCM n <+>
              text "against" <+> prettyTCM t
            coerce (Sort $ Type n) (sort $ sSuc $ Type n) t

        e0@(A.App i q (Arg ai e))
          | A.Quote _ <- unScope q, visible ai -> do
          let quoted (A.Def x) = return x
              quoted (A.Macro x) = return x
              quoted (A.Proj o (AmbQ [x])) = return x
              quoted (A.Proj o (AmbQ xs))  = typeError $ GenericError $ "quote: Ambigous name: " ++ show xs
              quoted (A.Con (AmbQ [x])) = return x
              quoted (A.Con (AmbQ xs))  = typeError $ GenericError $ "quote: Ambigous name: " ++ show xs
              quoted (A.ScopedExpr _ e) = quoted e
              quoted _                  = typeError $ GenericError $ "quote: not a defined name"
          x <- quoted (namedThing e)
          ty <- qNameType
          coerce (quoteName x) ty t

          | A.QuoteTerm _ <- unScope q ->
             do (et, _)   <- inferExpr (namedThing e)
                et'       <- etaContract =<< instantiateFull et
                let metas = allMetas et'
                case metas of
                  _:_ -> postponeTypeCheckingProblem (CheckExpr e0 t) $ andM $ map isInstantiatedMeta metas
                  []  -> do
                    q  <- quoteTerm et'
                    ty <- el primAgdaTerm
                    coerce q ty t

        A.Quote _ -> typeError $ GenericError "quote must be applied to a defined name"
        A.QuoteTerm _ -> typeError $ GenericError "quoteTerm must be applied to a term"
        A.Unquote _ -> typeError $ GenericError "unquote must be applied to a term"

        A.AbsurdLam i h -> checkAbsurdLambda i h e t

        A.ExtendedLam i di qname cs -> checkExtendedLambda i di qname cs e t

        A.Lam i (A.DomainFull (A.TypedBindings _ b)) e -> checkLambda b e t

        A.Lam i (A.DomainFree info x) e0 -> checkExpr (A.Lam i (domainFree info x) e0) t

        A.Lit lit    -> checkLiteral lit t
        A.Let i ds e -> checkLetBindings ds $ checkExpr e t
        A.Pi _ tel e | null tel -> checkExpr e t
        A.Pi _ tel e -> do
            (t0, t') <- checkPiTelescope tel $ \ tel -> do
                    t0  <- instantiateFull =<< isType_ e
                    tel <- instantiateFull tel
                    return (t0, telePi tel t0)
            noFunctionsIntoSize t0 t'
            let s = getSort t'
                v = unEl t'
            when (s == Inf) $ reportSDoc "tc.term.sort" 20 $
              vcat [ text ("reduced to omega:")
                   , nest 2 $ text "t   =" <+> prettyTCM t'
                   , nest 2 $ text "cxt =" <+> (prettyTCM =<< getContextTelescope)
                   ]
            coerce v (sort s) t
        A.Fun _ (Arg info a) b -> do
            a' <- isType_ a
            b' <- isType_ b
            s <- ptsRule a' b'
            let v = Pi (Dom info a') (NoAbs underscore b')
            noFunctionsIntoSize b' $ El s v
            coerce v (sort s) t
        A.Set _ n    -> do
          coerce (Sort $ mkType n) (sort $ mkType $ n + 1) t
        A.Prop _     -> do
          typeError $ GenericError "Prop is no longer supported"

        A.Rec _ fs  -> checkRecordExpression fs e t

        A.RecUpdate ei recexpr fs -> checkRecordUpdate ei recexpr fs e t

        A.DontCare e -> -- resurrect vars
          ifM ((Irrelevant ==) <$> asks envRelevance)
            (dontCare <$> do applyRelevanceToContext Irrelevant $ checkExpr e t)
            (internalError "DontCare may only appear in irrelevant contexts")

        e0@(A.QuoteGoal _ x e) -> do
          qg <- quoteGoal t
          case qg of
            Left metas -> postponeTypeCheckingProblem (CheckExpr e0 t) $ andM $ map isInstantiatedMeta metas
            Right quoted -> do
              tmType <- agdaTermType
              (v, ty) <- addLetBinding defaultArgInfo x quoted tmType (inferExpr e)
              coerce v ty t
        e0@(A.QuoteContext _) -> do
          qc <- quoteContext
          case qc of
            Left metas -> postponeTypeCheckingProblem (CheckExpr e0 t) $ andM $ map isInstantiatedMeta metas
            Right quotedContext -> do
              ctxType <- el $ list $ primArg <@> (unEl <$> agdaTypeType)
              coerce quotedContext ctxType t
        e0@(A.Tactic i e xs ys) -> do
          qc <- quoteContext
          qg <- quoteGoal t
          let postpone metas = postponeTypeCheckingProblem (CheckExpr e0 t) $ andM $ map isInstantiatedMeta metas
          case (qc, qg) of
            (Left metas1, Left metas2) -> postpone $ metas1 ++ metas2
            (Left metas , Right _    ) -> postpone $ metas
            (Right _    , Left metas ) -> postpone $ metas
            (Right quotedCtx, Right quotedGoal) -> do
              quotedCtx  <- defaultNamedArg <$> reify quotedCtx
              quotedGoal <- defaultNamedArg <$> reify quotedGoal
              let tac    = foldl (A.App i) (A.App i (A.App i e quotedCtx) quotedGoal) xs
                  result = foldl (A.App i) (A.Unquote i) (defaultNamedArg tac : ys)
              checkExpr result t

        A.ETel _   -> __IMPOSSIBLE__

        A.Dot{} -> typeError $ GenericError $ "Invalid dotted expression"

        -- Application
        _   | Application hd args <- appView e -> checkApplication hd args e t

  where
  -- | Call checkExpr with an hidden lambda inserted if appropriate,
  --   else fallback.
  tryInsertHiddenLambda :: A.Expr -> Type -> TCM Term -> TCM Term
  tryInsertHiddenLambda e t fallback
    -- Insert hidden lambda if all of the following conditions are met:
        -- type is a hidden function type, {x : A} -> B or {{x : A}} -> B
    | Pi (Dom info a) b <- ignoreSharing $ unEl t
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
          Just (BoundedLt u) -> ifBlocked u (\ _ _ -> fallback) $ \ v -> do
            ifM (checkSizeNeverZero v) proceed fallback
          _ -> proceed

    | otherwise = fallback

    where
    re = getRange e
    rx = caseMaybe (rStart re) noRange $ \ pos -> posToRange pos pos

    doInsert info y = do
      x <- unshadowName <=< freshName rx $ notInScopeName y
      reportSLn "tc.term.expr.impl" 15 $ "Inserting implicit lambda"
      checkExpr (A.Lam (A.ExprRange re) (domainFree info x) e) t

    hiddenLambdaOrHole h e = case e of
      A.AbsurdLam _ h'        -> h == h'
      A.ExtendedLam _ _ _ cls -> any hiddenLHS cls
      A.Lam _ bind _          -> h == getHiding bind
      A.QuestionMark{}        -> True
      _                       -> False

    hiddenLHS (A.Clause (A.LHS _ (A.LHSHead _ (a : _)) _) _ _ _ _) = notVisible a
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

-- | DOCUMENT ME!
quoteGoal :: Type -> TCM (Either [MetaId] Term)
quoteGoal t = do
  t' <- etaContract =<< instantiateFull t
  let metas = allMetas t'
  case metas of
    _:_ -> return $ Left metas
    []  -> do
      quotedGoal <- quoteTerm (unEl t')
      return $ Right quotedGoal

-- | DOCUMENT ME!
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
unquoteM :: A.Expr -> Term -> Type -> TCM Term -> TCM Term
unquoteM tac hole holeType k = do
  tac <- checkExpr tac =<< (el primAgdaTerm --> el (primAgdaTCM <#> primLevelZero <@> primUnit))
  inFreshModuleIfFreeParams $ unquoteTactic tac hole holeType k

-- | DOCUMENT ME!
unquoteTactic :: Term -> Term -> Type -> TCM Term -> TCM Term
unquoteTactic tac hole goal k = do
  ok  <- runUnquoteM $ unquoteTCM tac hole
  case ok of
    Left (BlockedOnMeta oldState x) -> do
      put oldState
      mi <- Map.lookup x <$> getMetaStore
      (r, unblock) <- case mi of
        Nothing -> do -- fresh meta: need to block on something else!
          otherMetas <- allMetas <$> instantiateFull goal
          case otherMetas of
            []  -> return (noRange,     return False) -- Nothing to block on, leave it yellow. Alternative: fail.
            x:_ -> return (noRange,     isInstantiatedMeta x)  -- range?
        Just mi -> return (getRange mi, isInstantiatedMeta x)
      setCurrentRange r $
        postponeTypeCheckingProblem (UnquoteTactic tac hole goal) unblock
    Left err -> typeError $ UnquoteFailed err
    Right _ -> k

---------------------------------------------------------------------------
-- * Projections
---------------------------------------------------------------------------

-- | Inferring the type of an overloaded projection application.
--   See 'inferOrCheckProjApp'.

inferProjApp :: A.Expr -> ProjOrigin -> [QName] -> A.Args -> TCM (Term, Type)
inferProjApp e o ds args0 = inferOrCheckProjApp e o ds args0 Nothing

-- | Checking the type of an overloaded projection application.
--   See 'inferOrCheckProjApp'.

checkProjApp  :: A.Expr -> ProjOrigin -> [QName] -> A.Args -> Type -> TCM Term
checkProjApp e o ds args0 t = do
  (v, ti) <- inferOrCheckProjApp e o ds args0 (Just t)
  coerce v ti t

-- | Inferring or Checking an overloaded projection application.
--
--   The overloaded projection is disambiguated by inferring the type of its
--   principal argument, which is the first visible argument.

inferOrCheckProjApp
  :: A.Expr
     -- ^ The whole expression which constitutes the application.
  -> ProjOrigin
     -- ^ The origin of the projection involved in this projection application.
  -> [QName]
     -- ^ The projection name (potentially ambiguous).  List must not be empty.
  -> A.Args
     -- ^ The arguments to the projection.
  -> Maybe Type
     -- ^ The expected type of the expression (if 'Nothing', infer it).
  -> TCM (Term, Type)
     -- ^ The type-checked expression and its type (if successful).
inferOrCheckProjApp e o ds args mt = do
  reportSDoc "tc.proj.amb" 20 $ vcat
    [ text "checking ambiguous projection"
    , text $ "  ds   = " ++ show ds
    , text   "  args = " <+> sep (map prettyTCM args)
    , text   "  t    = " <+> caseMaybe mt (text "Nothing") prettyTCM
    ]

  let refuse :: String -> TCM (Term, Type)
      refuse reason = typeError $ GenericError $
        "Cannot resolve overloaded projection "
        ++ show (A.nameConcrete $ A.qnameName $ head ds)
        ++ " because " ++ reason
      refuseNotApplied = refuse "it is not applied to a visible argument"
      refuseNoMatching = refuse "no matching candidate found"
      refuseNotRecordType = refuse "principal argument is not of record type"

      -- Postpone the whole type checking problem
      -- if type of principal argument (or the type where we get it from)
      -- is blocked by meta m.
      postpone m = do
        tc <- caseMaybe mt newTypeMeta_ return
        v <- postponeTypeCheckingProblem (CheckExpr e tc) $ isInstantiatedMeta m
        return (v, tc)

  -- The following cases need to be considered:
  -- 1. No arguments to the projection.
  -- 2. Arguments (parameters), but not the principal argument.
  -- 3. Argument(s) including the principal argument.

  -- For now, we only allow ambiguous projections if the first visible
  -- argument is the record value.

  case filter (visible . getHiding . snd) $ zip [0..] args of

    -- Case: we have no visible argument to the projection.
    -- In inference mode, we really need the visible argument, postponing does not help
    [] -> caseMaybe mt refuseNotApplied $ \ t -> do
      -- If we have the type, we can try to get the type of the principal argument.
      -- It is the first visible argument.
      TelV _ptel core <- telViewUpTo' (-1) (not . visible) t
      ifBlockedType core (\ m _ -> postpone m) $ {-else-} \ core -> do
      ifNotPiType core (\ _ -> refuseNotApplied) $ {-else-} \ dom _b -> do
      ifBlockedType (unDom dom) (\ m _ -> postpone m) $ {-else-} \ ta -> do
      caseMaybeM (isRecordType ta) refuseNotRecordType $ \ (_q, _pars, defn) -> do
      case defn of
        Record { recFields = fs } -> do
          case catMaybes $ for fs $ \ (Arg _ f) -> find (f ==) ds of
            [] -> refuseNoMatching
            [d] -> do
              storeDisambiguatedName d
              (,t) <$> checkHeadApplication e t (A.Proj o $ AmbQ [d]) args
            _ -> __IMPOSSIBLE__
        _ -> __IMPOSSIBLE__

    -- Case: we have a visible argument
    ((k, arg) : _) -> do
      (v0, ta) <- inferExpr $ namedArg arg
      reportSDoc "tc.proj.amb" 25 $ vcat
        [ text "  principal arg " <+> prettyTCM arg
        , text "  has type "      <+> prettyTCM ta
        ]
      -- ta should be a record type (after introducing the hidden args in v0)
      (vargs, ta) <- implicitArgs (-1) (not . visible) ta
      let v = v0 `apply` vargs
      ifBlockedType ta (\ m _ -> postpone m) {-else-} $ \ ta -> do
      caseMaybeM (isRecordType ta) refuseNotRecordType $ \ (q, _pars0, _) -> do

          -- try to project it with all of the possible projections
          let try d = do
              reportSDoc "tc.proj.amb" 30 $ vcat
                [ text $ "trying projection " ++ show d
                , text "  td  = " <+> caseMaybeM (getDefType d ta) (text "Nothing") prettyTCM
                ]

              -- get the original projection name
              isP <- isProjection d
              reportSDoc "tc.proj.amb" 40 $ vcat $
                [ text $ "  isProjection = " ++ caseMaybe isP "no" (const "yes")
                ] ++ caseMaybe isP [] (\ Projection{ projProper = proper, projOrig = orig } ->
                [ text $ "  proper       = " ++ show proper
                , text $ "  orig         = " ++ show orig
                ])

              -- Andreas, 2017-01-21, issue #2422
              -- The scope checker considers inherited projections (from nested records)
              -- as projections and allows overloading.  However, since they are defined
              -- as *composition* of projections, the type checker does *not* recognize them,
              -- and @isP@ will be @Nothing@.
              -- However, we can ignore this, as we only need the @orig@inal projection name
              -- for removing false ambiguity.  Thus, we skip these checks:

              -- Projection{ projProper = proper, projOrig = orig } <- MaybeT $ return isP
              -- guard $ isJust proper
              let orig = caseMaybe isP d projOrig

              -- try to eliminate
              (dom, u, tb) <- MaybeT (projectTyped v ta o d `catchError` \ _ -> return Nothing)
              reportSDoc "tc.proj.amb" 30 $ vcat
                [ text "  dom = " <+> prettyTCM dom
                , text "  u   = " <+> prettyTCM u
                , text "  tb  = " <+> prettyTCM tb
                ]
              (q', pars, _) <- MaybeT $ isRecordType $ unDom dom
              reportSDoc "tc.proj.amb" 30 $ vcat
                [ text "  q   = " <+> prettyTCM q
                , text "  q'  = " <+> prettyTCM q'
                ]
              guard (q == q')
              -- Get the type of the projection and check
              -- that the first visible argument is the record value.
              tfull <- lift $ defType <$> getConstInfo d
              TelV tel _ <- lift $ telViewUpTo' (-1) (not . visible) tfull
              reportSDoc "tc.proj.amb" 30 $ vcat
                [ text $ "  size tel  = " ++ show (size tel)
                , text $ "  size pars = " ++ show (size pars)
                ]
              -- See issue 1960 for when the following assertion fails for
              -- the correct disambiguation.
              -- guard (size tel == size pars)
              return (orig, (d, (pars, (dom, u, tb))))

          cands <- groupOn fst . catMaybes <$> mapM (runMaybeT . try) ds
          case cands of
            [] -> refuseNoMatching
            [[]] -> refuseNoMatching
            (_:_:_) -> refuse $ "several matching candidates found: "
                 ++ show (map (fst . snd) $ concat cands)
            -- case: just one matching projection d
            -- the term u = d v
            -- the type tb is the type of this application
            [ (_orig, (d, (pars, (_dom,u,tb)))) : _ ] -> do
              storeDisambiguatedName d

              -- Check parameters
              tfull <- typeOfConst d
              (_,_) <- checkKnownArguments (take k args) pars tfull

              -- Check remaining arguments
              let tc = fromMaybe typeDontCare mt
              let r  = getRange e
              z <- runExceptT $ checkArguments ExpandLast r (drop (k+1) args) tb tc
              case z of
                Right (us, trest) -> return (u `apply` us, trest)
                -- We managed to check a part of es and got us1, but es2 remain.
                Left (us1, es2, trest1) -> do
                  -- In the inference case:
                  -- To create a postponed type checking problem,
                  -- we do not use typeDontCare, but create a meta.
                  tc <- caseMaybe mt newTypeMeta_ return
                  v <- postponeTypeCheckingProblem_ $
                    CheckArgs ExpandLast r es2 trest1 tc $ \ us2 trest ->
                      coerce (u `apply` us1 `apply` us2) trest tc
                  return (v, tc)


-- | @checkApplication hd args e t@ checks an application.
--   Precondition: @Application hs args = appView e@
--
--   @checkApplication@ disambiguates constructors
--   (and continues to 'checkConstructorApplication')
--   and resolves pattern synonyms.
checkApplication :: A.Expr -> A.Args -> A.Expr -> Type -> TCM Term
checkApplication hd args e t = do
  reportSDoc "tc.check.app" 20 $ vcat
    [ text "checkApplication"
    , nest 2 $ text "hd   = " <+> prettyA hd
    , nest 2 $ text "args = " <+> sep (map prettyA args)
    , nest 2 $ text "e    = " <+> prettyA e
    , nest 2 $ text "t    = " <+> prettyTCM t
    ]
  reportSDoc "tc.check.app" 70 $ vcat
    [ text "checkApplication (raw)"
    , nest 2 $ text $ "hd   = " ++ show hd
    , nest 2 $ text $ "args = " ++ show (deepUnscope args)
    , nest 2 $ text $ "e    = " ++ show (deepUnscope e)
    , nest 2 $ text $ "t    = " ++ show t
    ]
  case unScope hd of
    A.Proj _ (AmbQ []) -> __IMPOSSIBLE__

    -- Subcase: unambiguous projection
    A.Proj _ (AmbQ [_]) -> checkHeadApplication e t hd args

    -- Subcase: ambiguous projection
    A.Proj o (AmbQ ds@(_:_:_)) -> checkProjApp e o ds args t

    -- Subcase: ambiguous constructor
    A.Con (AmbQ cs@(_:_:_)) -> do
      -- First we should figure out which constructor we want.
      reportSLn "tc.check.term" 40 $ "Ambiguous constructor: " ++ show cs

      -- Get the datatypes of the various constructors
      let getData Constructor{conData = d} = d
          getData _                        = __IMPOSSIBLE__
      reportSLn "tc.check.term" 40 $ "  ranges before: " ++ show (getRange cs)
      -- We use the reduced constructor when disambiguating, but
      -- the original constructor for type checking. This is important
      -- since they may have different types (different parameters).
      -- See issue 279.
      cons  <- mapM getConForm cs
      reportSLn "tc.check.term" 40 $ "  reduced: " ++ show cons
      dcs <- zipWithM (\ c con -> (, setConName c con) . getData . theDef <$> getConInfo con) cs cons
      -- Type error
      let badCon t = typeError $ DoesNotConstructAnElementOf (head cs) t
      -- Lets look at the target type at this point
      let getCon :: TCM (Maybe ConHead)
          getCon = do
            TelV tel t1 <- telView t
            addContext tel $ do
             reportSDoc "tc.check.term.con" 40 $ nest 2 $
               text "target type: " <+> prettyTCM t1
             ifBlockedType t1 (\ m t -> return Nothing) $ \ t' ->
               caseMaybeM (isDataOrRecord $ unEl t') (badCon t') $ \ d ->
                 case [ c | (d', c) <- dcs, d == d' ] of
                   [c] -> do
                     reportSLn "tc.check.term" 40 $ "  decided on: " ++ show c
                     storeDisambiguatedName $ conName c
                     return $ Just c
                   []  -> badCon $ t' $> Def d []
                   cs  -> typeError $ CantResolveOverloadedConstructorsTargetingSameDatatype d $ map conName cs
      let unblock = isJust <$> getCon -- to unblock, call getCon later again
      mc <- getCon
      case mc of
        Just c  -> checkConstructorApplication e t c args
        Nothing -> postponeTypeCheckingProblem (CheckExpr e t) unblock

    -- Subcase: non-ambiguous constructor
    A.Con (AmbQ [c]) -> do
      -- augment c with record fields, but do not revert to original name
      con <- getOrigConHead c
      checkConstructorApplication e t con args

    -- Subcase: pattern synonym
    A.PatternSyn n -> do
      (ns, p) <- lookupPatternSyn n
      p <- setRange (getRange n) . killRange <$> expandPatternSynonyms (vacuous p)  -- expand recursive pattern synonyms
      -- Expand the pattern synonym by substituting for
      -- the arguments we have got and lambda-lifting
      -- over the ones we haven't.
      let meta r = A.Underscore $ A.emptyMetaInfo{ A.metaRange = r }   -- TODO: name suggestion
      case A.insertImplicitPatSynArgs meta (getRange n) ns args of
        Nothing      -> typeError $ BadArgumentsToPatternSynonym n
        Just (s, ns) -> do
          let p' = A.patternToExpr p
              e' = A.lambdaLiftExpr (map unArg ns) (A.substExpr s p')
          checkExpr e' t

    -- Subcase: macro
    A.Macro x -> do
      -- First go: no parameters
      TelV tel _ <- telView =<< normalise . defType =<< instantiateDef =<< getConstInfo x

      tTerm <- primAgdaTerm
      tName <- primQName

      let argTel   = init $ telToList tel -- last argument is the hole term

          -- inspect macro type to figure out if arguments need to be wrapped in quote/quoteTerm
          mkArg :: Type -> NamedArg A.Expr -> NamedArg A.Expr
          mkArg t a | unEl t == tTerm =
            (fmap . fmap)
              (A.App (A.ExprRange (getRange a)) (A.QuoteTerm A.exprNoRange) . defaultNamedArg) a
          mkArg t a | unEl t == tName =
            (fmap . fmap)
              (A.App (A.ExprRange (getRange a)) (A.Quote A.exprNoRange) . defaultNamedArg) a
          mkArg t a | otherwise = a

          makeArgs :: [Dom (String, Type)] -> [NamedArg A.Expr] -> ([NamedArg A.Expr], [NamedArg A.Expr])
          makeArgs [] args = ([], args)
          makeArgs _  []   = ([], [])
          makeArgs tel@(d : _) (arg : args) =
            case insertImplicit arg (map (fmap fst . argFromDom) tel) of
              ImpInsert is   -> makeArgs (drop (length is) tel) (arg : args)
              BadImplicits   -> (arg : args, [])  -- fail later in checkHeadApplication
              NoSuchName{}   -> (arg : args, [])  -- ditto
              NoInsertNeeded -> first (mkArg (snd $ unDom d) arg :) $ makeArgs (tail tel) args

          (macroArgs, otherArgs) = makeArgs argTel args
          unq = A.App (A.ExprRange $ fuseRange x args) (A.Unquote A.exprNoRange) . defaultNamedArg

          desugared = A.app (unq $ unAppView $ Application (A.Def x) $ macroArgs) otherArgs

      checkExpr desugared t

    -- Subcase: unquote
    A.Unquote _
      | [arg] <- args -> do
          (_, hole) <- newValueMeta RunMetaOccursCheck t
          unquoteM (namedArg arg) hole t $ return hole
      | arg : args <- args -> do
          -- Example: unquote v a b : A
          --  Create meta H : (x : X) (y : Y x) → Z x y for the hole
          --  Check a : X, b : Y a
          --  Unify Z a b == A
          --  Run the tactic on H
          tel    <- metaTel args                    -- (x : X) (y : Y x)
          target <- addContext' tel newTypeMeta_      -- Z x y
          let holeType = telePi_ tel target         -- (x : X) (y : Y x) → Z x y
          (vs, EmptyTel) <- checkArguments_ ExpandLast (getRange args) args tel
                                                    -- a b : (x : X) (y : Y x)
          let rho = reverse (map unArg vs) ++# IdS  -- [x := a, y := b]
          equalType (applySubst rho target) t       -- Z a b == A
          (_, hole) <- newValueMeta RunMetaOccursCheck holeType
          unquoteM (namedArg arg) hole holeType $ return $ apply hole vs
      where
        metaTel :: [Arg a] -> TCM Telescope
        metaTel []           = pure EmptyTel
        metaTel (arg : args) = do
          a <- newTypeMeta_
          let dom = a <$ domFromArg arg
          ExtendTel dom . Abs "x" <$> addContext' ("x", dom) (metaTel args)

    -- Subcase: defined symbol or variable.
    _ -> do
      v <- checkHeadApplication e t hd args
      reportSDoc "tc.term.app" 30 $ vcat
        [ text "checkApplication: checkHeadApplication returned"
        , nest 2 $ text "v = " <+> prettyTCM v
        ]
      return v

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | Check an interaction point without arguments.
checkQuestionMark :: (Type -> TCM (MetaId, Term)) -> Type -> A.MetaInfo -> InteractionId -> TCM Term
checkQuestionMark new t0 i ii = do
  reportSDoc "tc.interaction" 20 $ sep
    [ text "Found interaction point"
    , text (show ii)
    , text ":"
    , prettyTCM t0
    ]
  reportSDoc "tc.interaction" 60 $ sep
    [ text "Raw:"
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
inferMeta :: (Type -> TCM (MetaId, Term)) -> A.MetaInfo -> TCM (Args -> Term, Type)
inferMeta newMeta i = mapFst apply <$> checkOrInferMeta newMeta Nothing i

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
      t' <- jMetaType . mvJudgement <$> lookupMeta x
      case mt of
        Nothing -> return (v, t')
        Just t  -> (,t) <$> coerce v t' t

-- | Turn a domain-free binding (e.g. lambda) into a domain-full one,
--   by inserting an underscore for the missing type.
domainFree :: ArgInfo -> A.Name -> A.LamBinding
domainFree info x =
  A.DomainFull $ A.TypedBindings r $ Arg info $ A.TBind r [pure x] $ A.Underscore underscoreInfo
  where
    r = getRange x
    underscoreInfo = A.MetaInfo
      { A.metaRange          = r
      , A.metaScope          = emptyScopeInfo
      , A.metaNumber         = Nothing
      , A.metaNameSuggestion = show $ A.nameConcrete x
      }

---------------------------------------------------------------------------
-- * Applications
---------------------------------------------------------------------------

inferHeadDef :: ProjOrigin -> QName -> TCM (Args -> Term, Type)
inferHeadDef o x = do
  proj <- isProjection x
  let app =
        case proj of
          Nothing -> \ args -> Def x $ map Apply args
          Just p  -> \ args -> projDropParsApply p o args
  mapFst apply <$> inferDef app x

-- | Infer the type of a head thing (variable, function symbol, or constructor).
--   We return a function that applies the head to arguments.
--   This is because in case of a constructor we want to drop the parameters.
inferHead :: A.Expr -> TCM (Args -> Term, Type)
inferHead e = do
  case e of
    (A.Var x) -> do -- traceCall (InferVar x) $ do
      (u, a) <- getVarInfo x
      reportSDoc "tc.term.var" 20 $ hsep
        [ text "variable" , text (show x)
        , text "(" , text (show u) , text ")"
        , text "has type:" , text (show a)
        ]
      when (unusableRelevance $ getRelevance a) $
        typeError $ VariableIsIrrelevant x
      return (apply u, unDom a)
    (A.Def x) -> inferHeadDef ProjPrefix x
    (A.Proj o (AmbQ [d])) -> inferHeadDef o d
    (A.Proj{}) -> __IMPOSSIBLE__ -- inferHead will only be called on unambiguous projections
    (A.Con (AmbQ [c])) -> do

      -- Constructors are polymorphic internally.
      -- So, when building the constructor term
      -- we should throw away arguments corresponding to parameters.

      -- First, inferDef will try to apply the constructor
      -- to the free parameters of the current context. We ignore that.
      con <- getOrigConHead c
      (u, a) <- inferDef (\ _ -> Con con ConOCon []) c

      -- Next get the number of parameters in the current context.
      Constructor{conPars = n} <- theDef <$> (instantiateDef =<< getConstInfo c)

      reportSLn "tc.term.con" 7 $ unwords [show c, "has", show n, "parameters."]

      -- So when applying the constructor throw away the parameters.
      return (apply u . genericDrop n, a)
    (A.Con _) -> __IMPOSSIBLE__  -- inferHead will only be called on unambiguous constructors
    (A.QuestionMark i ii) -> inferMeta (newQuestionMark ii) i
    (A.Underscore i)   -> inferMeta (newValueMeta RunMetaOccursCheck) i
    e -> do
      (term, t) <- inferExpr e
      return (apply term, t)

inferDef :: (Args -> Term) -> QName -> TCM (Term, Type)
inferDef mkTerm x =
    traceCall (InferDef x) $ do
    -- getConstInfo retrieves the *absolute* (closed) type of x
    -- instantiateDef relativizes it to the current context
    d  <- instantiateDef =<< getConstInfo x
    -- irrelevant defs are only allowed in irrelevant position
    let drel = defRelevance d
    when (drel /= Relevant) $ do
      rel <- asks envRelevance
      reportSDoc "tc.irr" 50 $ vcat
        [ text "declaration relevance =" <+> text (show drel)
        , text "context     relevance =" <+> text (show rel)
        ]
      unless (drel `moreRelevant` rel) $ typeError $ DefinitionIsIrrelevant x
    -- since x is considered living in the top-level, we have to
    -- apply it to the current context
    vs <- freeVarsToApply x
    reportSDoc "tc.term.def" 10 $ do
      text "inferred def " <+> prettyTCM x <+> hsep (map prettyTCM vs)
    let t = defType d
    reportSDoc "tc.term.def" 10 $ nest 2 $ text " : " <+> prettyTCM t
    let v = mkTerm vs -- applies x to vs, dropping parameters
    reportSDoc "tc.term.def" 10 $ nest 2 $ text " --> " <+> prettyTCM v
    return (v, t)

-- | Check the type of a constructor application. This is easier than
--   a general application since the implicit arguments can be inserted
--   without looking at the arguments to the constructor.
checkConstructorApplication :: A.Expr -> Type -> ConHead -> [NamedArg A.Expr] -> TCM Term
checkConstructorApplication org t c args = do
  reportSDoc "tc.term.con" 50 $ vcat
    [ text "entering checkConstructorApplication"
    , nest 2 $ vcat
      [ text "org  =" <+> prettyTCM org
      , text "t    =" <+> prettyTCM t
      , text "c    =" <+> prettyTCM c
      , text "args =" <+> prettyTCM args
    ] ]
  let paramsGiven = checkForParams args
  if paramsGiven then fallback else do
    reportSDoc "tc.term.con" 50 $ text "checkConstructorApplication: no parameters explicitly supplied, continuing..."
    cdef  <- getConInfo c
    let Constructor{conData = d, conPars = npars} = theDef cdef
    reportSDoc "tc.term.con" 50 $ nest 2 $ text "d    =" <+> prettyTCM d
    -- Issue 661: t maybe an evaluated form of d .., so we evaluate d
    -- as well and then check wether we deal with the same datatype
    t0 <- reduce (Def d [])
    case (ignoreSharing t0, ignoreSharing $ unEl t) of -- Only fully applied constructors get special treatment
      (Def d0 _, Def d' es) -> do
        let ~(Just vs) = allApplyElims es
        reportSDoc "tc.term.con" 50 $ nest 2 $ text "d0   =" <+> prettyTCM d0
        reportSDoc "tc.term.con" 50 $ nest 2 $ text "d'   =" <+> prettyTCM d'
        reportSDoc "tc.term.con" 50 $ nest 2 $ text "vs   =" <+> prettyTCM vs
        if d' /= d0 then fallback else do
         -- Issue 661: d' may take more parameters than d, in particular
         -- these additional parameters could be a module parameter telescope.
         -- Since we get the constructor type ctype from d but the parameters
         -- from t = Def d' vs, we drop the additional parameters.
         npars' <- getNumberOfParameters d'
         caseMaybe (sequenceA $ List2 (Just npars, npars')) fallback $ \ (List2 (n, n')) -> do
           reportSDoc "tc.term.con" 50 $ nest 2 $ text $ "n    = " ++ show n
           reportSDoc "tc.term.con" 50 $ nest 2 $ text $ "n'   = " ++ show n'
           when (n > n')  -- preprocessor does not like ', so put on next line
             __IMPOSSIBLE__
           let ps    = genericTake n $ genericDrop (n' - n) vs
               ctype = defType cdef
           reportSDoc "tc.term.con" 20 $ vcat
             [ text "special checking of constructor application of" <+> prettyTCM c
             , nest 2 $ vcat [ text "ps     =" <+> prettyTCM ps
                             , text "ctype  =" <+> prettyTCM ctype ] ]
           let ctype' = ctype `piApply` ps
           reportSDoc "tc.term.con" 20 $ nest 2 $ text "ctype' =" <+> prettyTCM ctype'
           -- get the parameter names
           let TelV ptel _ = telView'UpTo n ctype
           let pnames = map (fmap fst) $ telToList ptel
           -- drop the parameter arguments
               args' = dropArgs pnames args
           -- check the non-parameter arguments
           expandLast <- asks envExpandLast
           checkArguments' expandLast (getRange c) args' ctype' t $ \us t' -> do
             reportSDoc "tc.term.con" 20 $ nest 2 $ vcat
               [ text "us     =" <+> prettyTCM us
               , text "t'     =" <+> prettyTCM t' ]
             coerce (Con c ConOCon us) t' t
      _ -> do
        reportSDoc "tc.term.con" 50 $ nest 2 $ text "we are not at a datatype, falling back"
        fallback
  where
    fallback = checkHeadApplication org t (A.Con (AmbQ [conName c])) args

    -- Check if there are explicitly given hidden arguments,
    -- in which case we fall back to default type checking.
    -- We could work harder, but let's not for now.
    --
    -- Andreas, 2012-04-18: if all inital args are underscores, ignore them
    checkForParams args =
      let (hargs, rest) = span (not . visible) args
          notUnderscore A.Underscore{} = False
          notUnderscore _              = True
      in  any notUnderscore $ map (unScope . namedArg) hargs

    -- Drop the constructor arguments that correspond to parameters.
    dropArgs [] args                = args
    dropArgs ps []                  = args
    dropArgs ps args@(arg : args')
      | Just p   <- name,
        Just ps' <- namedPar p ps   = dropArgs ps' args'
      | Nothing  <- name,
        Just ps' <- unnamedPar h ps = dropArgs ps' args'
      | otherwise                   = args
      where
        name = fmap rangedThing . nameOf $ unArg arg
        h    = getHiding arg

        namedPar   x = dropPar ((x ==) . unDom)
        unnamedPar h = dropPar ((h ==) . getHiding)

        dropPar this (p : ps) | this p    = Just ps
                              | otherwise = dropPar this ps
        dropPar _ [] = Nothing


{- UNUSED CODE, BUT DON'T REMOVE (2012-04-18)

    -- Split the arguments to a constructor into those corresponding
    -- to parameters and those that don't. Dummy underscores are inserted
    -- for parameters that are not given explicitly.
    splitArgs [] args = ([], args)
    splitArgs ps []   =
          (map (const dummyUnderscore) ps, args)
    splitArgs ps args@(Arg NotHidden _ _ : _) =
          (map (const dummyUnderscore) ps, args)
    splitArgs (p:ps) (arg : args)
      | elem mname [Nothing, Just p] =
          mapFst (arg :) $ splitArgs ps args
      | otherwise =
          mapFst (dummyUnderscore :) $ splitArgs ps (arg:args)
      where
        mname = nameOf (unArg arg)

    dummyUnderscore = Arg Hidden Relevant (unnamed $ A.Underscore $ A.MetaInfo noRange emptyScopeInfo Nothing)
-}

-- | @checkHeadApplication e t hd args@ checks that @e@ has type @t@,
-- assuming that @e@ has the form @hd args@. The corresponding
-- type-checked term is returned.
--
-- If the head term @hd@ is a coinductive constructor, then a
-- top-level definition @fresh tel = hd args@ (where the clause is
-- delayed) is added, where @tel@ corresponds to the current
-- telescope. The returned term is @fresh tel@.
--
-- Precondition: The head @hd@ has to be unambiguous, and there should
-- not be any need to insert hidden lambdas.
checkHeadApplication :: A.Expr -> Type -> A.Expr -> [NamedArg A.Expr] -> TCM Term
checkHeadApplication e t hd args = do
  kit       <- coinductionKit
  case hd of
    A.Con (AmbQ [c]) | Just c == (nameOfSharp <$> kit) -> do
      -- Type checking # generated #-wrapper. The # that the user can write will be a Def,
      -- but the sharp we generate in the body of the wrapper is a Con.
      defaultResult
    A.Con (AmbQ [c]) -> do
      (f, t0) <- inferHead hd
      reportSDoc "tc.term.con" 5 $ vcat
        [ text "checkHeadApplication inferred" <+>
          prettyTCM c <+> text ":" <+> prettyTCM t0
        ]
      expandLast <- asks envExpandLast
      checkArguments' expandLast (getRange hd) args t0 t $ \vs t1 -> do
        TelV eTel eType <- telView t
        -- If the expected type @eType@ is a metavariable we have to make
        -- sure it's instantiated to the proper pi type
        TelV fTel fType <- telViewUpTo (size eTel) t1
        -- We know that the target type of the constructor (fType)
        -- does not depend on fTel so we can compare fType and eType
        -- first.

        when (size eTel > size fTel) $
          typeError $ UnequalTypes CmpLeq t1 t -- switch because of contravariance
          -- Andreas, 2011-05-10 report error about types rather  telescopes
          -- compareTel CmpLeq eTel fTel >> return () -- This will fail!

        reportSDoc "tc.term.con" 10 $ addContext eTel $ vcat
          [ text "checking" <+>
            prettyTCM fType <+> text "?<=" <+> prettyTCM eType
          ]
        blockTerm t $ f vs <$ workOnTypes (do
          addContext' eTel $ leqType fType eType
          compareTel t t1 CmpLeq eTel fTel)

    (A.Def c) | Just c == (nameOfSharp <$> kit) -> do
      arg <- case args of
               [a] | getHiding a == NotHidden -> return $ namedArg a
               _ -> typeError $ GenericError $ show c ++ " must be applied to exactly one argument."

      -- The name of the fresh function.
      i <- fresh :: TCM Int
      let name = filter (/= '_') (show $ A.nameConcrete $ A.qnameName c) ++ "-" ++ show i

      kit <- coinductionKit'
      let flat = nameOfFlat kit
          inf  = nameOfInf  kit

      -- Add the type signature of the fresh function to the
      -- signature.
      -- To make sure we can type check the generated function we have to make
      -- sure that its type is \inf. The reason for this is that we don't yet
      -- postpone checking of patterns when we don't know their types (Issue480).
      forcedType <- do
        lvl <- levelType
        (_, l) <- newValueMeta RunMetaOccursCheck lvl
        lv  <- levelView l
        (_, a) <- newValueMeta RunMetaOccursCheck (sort $ Type lv)
        return $ El (Type lv) $ Def inf [Apply $ setHiding Hidden $ defaultArg l, Apply $ defaultArg a]

      wrapper <- inFreshModuleIfFreeParams $ do
        c' <- setRange (getRange c) <$>
                liftM2 qualify (killRange <$> currentModule)
                               (freshName_ name)

        -- Define and type check the fresh function.
        rel <- asks envRelevance
        abs <- aModeToDef <$> asks envAbstractMode
        let info   = A.mkDefInfo (A.nameConcrete $ A.qnameName c') noFixity'
                                 PublicAccess abs noRange
            core   = A.LHSProj { A.lhsDestructor = AmbQ [flat]
                               , A.lhsFocus      = defaultNamedArg $ A.LHSHead c' []
                               , A.lhsPatsRight  = [] }
            clause = A.Clause (A.LHS (A.LHSRange noRange) core []) []
                              (A.RHS arg Nothing)
                              [] False

        i <- currentOrFreshMutualBlock

        -- If we are in irrelevant position, add definition irrelevantly.
        -- TODO: is this sufficient?
        addConstant c' =<< do
          let ai = setRelevance rel defaultArgInfo
          useTerPragma $
            (defaultDefn ai c' forcedType emptyFunction)
            { defMutual = i }

        checkFunDef NotDelayed info c' [clause]

        reportSDoc "tc.term.expr.coind" 15 $ do
          def <- theDef <$> getConstInfo c'
          vcat $
            [ text "The coinductive wrapper"
            , nest 2 $ prettyTCM rel <> prettyTCM c' <+> text ":"
            , nest 4 $ prettyTCM t
            , nest 2 $ prettyA clause
            , text "The definition is" <+> text (show $ funDelayed def) <>
              text "."
            ]
        return c'

      -- The application of the fresh function to the relevant
      -- arguments.
      e' <- Def wrapper . map Apply <$> getContextArgs

      reportSDoc "tc.term.expr.coind" 15 $ vcat $
          [ text "The coinductive constructor application"
          , nest 2 $ prettyTCM e
          , text "was translated into the application"
          , nest 2 $ prettyTCM e'
          ]

      blockTerm t $ e' <$ workOnTypes (leqType forcedType t)
    A.Con _  -> __IMPOSSIBLE__
    _ -> defaultResult
  where
  defaultResult = do
    (f, t0) <- inferHead hd
    expandLast <- asks envExpandLast
    checkArguments' expandLast (getRange hd) args t0 t $ \vs t1 -> do
      coerce (f vs) t1 t

traceCallE :: Call -> ExceptT e TCM r -> ExceptT e TCM r
traceCallE call m = do
  z <- lift $ traceCall call $ runExceptT m
  case z of
    Right e  -> return e
    Left err -> throwError err

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
  text "Invalid projection parameter " <+> prettyA arg
checkKnownArgument arg@(Arg info e) (Arg _infov v : vs) t = do
  (Dom info' a, b) <- mustBePi t
  -- Skip the arguments from vs that do not correspond to e
  if not (getHiding info == getHiding info'
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
  traceCall (CheckExprCall e t0) $ do
    reportSDoc "tc.term.args.named" 15 $ do
        text "Checking named arg" <+> sep
          [ fsep [ prettyTCM arg, text ":", prettyTCM t0 ]
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

-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t0'@ and @args : Delta@. Inserts hidden arguments to
--   make this happen.  Returns the evaluated arguments @vs@, the remaining
--   type @t0'@ (which should be a subtype of @t1@) and any constraints @cs@
--   that have to be solved for everything to be well-formed.

checkArguments :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  ExceptT (Args, [NamedArg A.Expr], Type) TCM (Args, Type)

-- Case: no arguments, do not insert trailing hidden arguments: We are done.
checkArguments DontExpandLast _ [] t0 t1 = return ([], t0)

-- Case: no arguments, but need to insert trailing hiddens.
checkArguments exh r [] t0 t1 =
    traceCallE (CheckArguments r [] t0 t1) $ lift $ do
      t1' <- unEl <$> reduce t1
      implicitArgs (-1) (expand t1') t0
    where
      expand (Pi (Dom info _) _)   Hidden = getHiding info /= Hidden &&
                                            exh == ExpandLast
      expand _                     Hidden = exh == ExpandLast
      expand (Pi (Dom info _) _) Instance = getHiding info /= Instance
      expand _                   Instance = True
      expand _                  NotHidden = False

-- Case: argument given.
checkArguments exh r args0@(arg@(Arg info e) : args) t0 t1 =
    traceCallE (CheckArguments r args0 t0 t1) $ do
      lift $ reportSDoc "tc.term.args" 30 $ sep
        [ text "checkArguments"
--        , text "  args0 =" <+> prettyA args0
        , nest 2 $ vcat
          [ text "e     =" <+> prettyA e
          , text "t0    =" <+> prettyTCM t0
          , text "t1    =" <+> prettyTCM t1
          ]
        ]
      -- First, insert implicit arguments, depending on current argument @arg@.
      let hx = getHiding info  -- hiding of current argument
          mx = fmap rangedThing $ nameOf e -- name of current argument
          -- do not insert visible arguments
          expand NotHidden y = False
          -- insert a hidden argument if arg is not hidden or has different name
          -- insert an instance argument if arg is not instance  or has different name
          expand hy        y = hy /= hx || maybe False (y /=) mx
      (nargs, t) <- lift $ implicitNamedArgs (-1) expand t0
      -- Separate names from args.
      let (mxs, us) = unzip $ map (\ (Arg ai (Named mx u)) -> (mx, Arg ai u)) nargs
          xs        = catMaybes mxs
      -- We are done inserting implicit args.  Now, try to check @arg@.
      ifBlockedType t (\ m t -> throwError (us, args0, t)) $ \ t0' -> do

        -- What can go wrong?

        -- 1. We ran out of function types.
        let shouldBePi
              -- a) It is an explicit argument, but we ran out of function types.
              | visible info = lift $ typeError $ ShouldBePi t0'
              -- b) It is an implicit argument, and we did not insert any implicits.
              --    Thus, the type was not a function type to start with.
              | null xs        = lift $ typeError $ ShouldBePi t0'
              -- c) We did insert implicits, but we ran out of implicit function types.
              --    Then, we should inform the user that we did not find his one.
              | otherwise      = lift $ typeError $ WrongNamedArgument arg

        -- 2. We have a function type left, but it is the wrong one.
        --    Our argument must be implicit, case a) is impossible.
        --    (Otherwise we would have ran out of function types instead.)
        let wrongPi
              -- b) We have not inserted any implicits.
              | null xs   = lift $ typeError $ WrongHidingInApplication t0'
              -- c) We inserted implicits, but did not find his one.
              | otherwise = lift $ typeError $ WrongNamedArgument arg

        -- t0' <- lift $ forcePi (getHiding info) (maybe "_" rangedThing $ nameOf e) t0'
        case ignoreSharing $ unEl t0' of
          Pi (Dom info' a) b
            | getHiding info == getHiding info'
              && (visible info || maybe True ((absName b ==) . rangedThing) (nameOf e)) -> do
                u <- lift $ applyRelevanceToContext (getRelevance info') $ do
                 -- Andreas, 2014-05-30 experiment to check non-dependent arguments
                 -- after the spine has been processed.  Allows to propagate type info
                 -- from ascribed type into extended-lambdas.  Would solve issue 1159.
                 -- However, leaves unsolved type checking problems in the test suite.
                 -- I do not know what I am doing wrong here.
                 -- Could be extreme order-sensitivity or my abuse of the postponing
                 -- mechanism.
                 -- Andreas, 2016-02-02: Ulf says unless there is actually some meta
                 -- blocking a postponed type checking problem, we might never retry,
                 -- since the trigger for retrying constraints is solving a meta.
                 -- Thus, the following naive use violates some invariant.
                 -- if not $ isBinderUsed b
                 -- then postponeTypeCheckingProblem (CheckExpr (namedThing e) a) (return True) else
                  let e' = e { nameOf = maybe (Just $ unranged $ absName b) Just (nameOf e) }
                  checkNamedArg (Arg info' e') a
                -- save relevance info' from domain in argument
                addCheckedArgs us (Arg info' u) $
                  checkArguments exh (fuseRange r e) args (absApp b u) t1
            | otherwise -> do
                reportSDoc "error" 10 $ nest 2 $ vcat
                  [ text $ "info      = " ++ show info
                  , text $ "info'     = " ++ show info'
                  , text $ "absName b = " ++ show (absName b)
                  , text $ "nameOf e  = " ++ show (nameOf e)
                  ]
                wrongPi
          _ -> shouldBePi
  where
    addCheckedArgs us u rec =
      (mapFst ((us ++) . (u :)) <$> rec)
        `catchError` \(vs, es, t) ->
          throwError (us ++ u : vs, es, t)

-- | Check that a list of arguments fits a telescope.
--   Inserts hidden arguments as necessary.
--   Returns the type-checked arguments and the remaining telescope.
checkArguments_
  :: ExpandHidden         -- ^ Eagerly insert trailing hidden arguments?
  -> Range                -- ^ Range of application.
  -> [NamedArg A.Expr]    -- ^ Arguments to check.
  -> Telescope            -- ^ Telescope to check arguments against.
  -> TCM (Args, Telescope)
     -- ^ Checked arguments and remaining telescope if successful.
checkArguments_ exh r args tel = do
    z <- runExceptT $
      checkArguments exh r args (telePi tel typeDontCare) typeDontCare
    case z of
      Right (args, t) -> do
        let TelV tel' _ = telView' t
        return (args, tel')
      Left _ -> __IMPOSSIBLE__  -- type cannot be blocked as it is generated by telePi


-- | Infer the type of an expression. Implemented by checking against a meta
--   variable.  Except for neutrals, for them a polymorphic type is inferred.
inferExpr :: A.Expr -> TCM (Term, Type)
-- inferExpr e = inferOrCheck e Nothing
inferExpr = inferExpr' DontExpandLast

inferExpr' :: ExpandHidden -> A.Expr -> TCM (Term, Type)
inferExpr' exh e = do
  let Application hd args = appView e
  reportSDoc "tc.infer" 30 $ vcat
    [ text "inferExpr': appView of " <+> prettyA e
    , text "  hd   = " <+> prettyA hd
    , text "  args = " <+> prettyAs args
    ]
  reportSDoc "tc.infer" 60 $ vcat
    [ text $ "  hd (raw) = " ++ show hd
    ]
  if not $ defOrVar hd then fallback else traceCall (InferExpr e) $ do
    case unScope $ hd of
      A.Proj o (AmbQ ds@(_:_:_)) -> inferProjApp e o ds args
      _ -> do
        (f, t0) <- inferHead hd
        res <- runExceptT $ checkArguments exh (getRange hd) args t0 (sort Prop)
        case res of
          Right (vs, t1) -> return (f vs, t1)
          Left t1 -> fallback -- blocked on type t1
  where
    fallback = do
      t <- workOnTypes $ newTypeMeta_
      v <- checkExpr e t
      return (v,t)

defOrVar :: A.Expr -> Bool
defOrVar A.Var{} = True
defOrVar A.Def{} = True
defOrVar A.Proj{} = True
defOrVar (A.ScopedExpr _ e) = defOrVar e
defOrVar _     = False

-- | Used to check aliases @f = e@.
--   Switches off 'ExpandLast' for the checking of top-level application.
checkDontExpandLast :: A.Expr -> Type -> TCM Term
checkDontExpandLast e t = case e of
  _ | Application hd args <- appView e,  defOrVar hd ->
    traceCall (CheckExprCall e t) $ localScope $ dontExpandLast $ shared =<< do
      checkApplication hd args e t
  _ -> checkExpr e t -- note that checkExpr always sets ExpandLast

{- Andreas, 2013-03-15 UNUSED, but don't remove
inferOrCheck :: A.Expr -> Maybe Type -> TCM (Term, Type)
inferOrCheck e mt = case e of
  _ | Application hd args <- appView e, defOrVar hd -> traceCall (InferExpr e) $ do
    (f, t0) <- inferHead hd
    res <- runErrorT $ checkArguments DontExpandLast
                                      (getRange hd) args t0 $
                                      maybe (sort Prop) id mt
    case res of
      Right (vs, t1) -> maybe (return (f vs, t1))
                              (\ t -> (,t) <$> coerce (f vs) t1 t)
                              mt
      Left t1        -> fallback -- blocked on type t1
  _ -> fallback
  where
    fallback = do
      t <- maybe (workOnTypes $ newTypeMeta_) return mt
      v <- checkExpr e t
      return (v,t)
-}

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
  reportSDoc "tc.with.infer" 20 $ text "inferExprforWith " <+> prettyTCM e
  reportSLn  "tc.with.infer" 80 $ "inferExprforWith " ++ show (deepUnscope e)
  traceCall (InferExpr e) $ do
    -- With wants type and term fully instantiated!
    (v, t) <- instantiateFull =<< inferExpr e
    v0 <- reduce v
    -- Andreas 2014-11-06, issue 1342.
    -- Check that we do not `with` on a module parameter!
    case ignoreSharing v0 of
      Var i [] -> whenM (isModuleFreeVar i) $ do
        reportSDoc "tc.with.infer" 80 $ vcat
          [ text $ "with expression is variable " ++ show i
          , text "current modules = " <+> do text . show =<< currentModule
          , text "current module free vars = " <+> do text . show =<< getCurrentModuleFreeVars
          , text "context size = " <+> do text . show =<< getContextSize
          , text "current context = " <+> do prettyTCM =<< getContextTelescope
          ]
        typeError $ WithOnFreeVariable e v0
      _        -> return ()
    -- Possibly insert hidden arguments.
    TelV tel t0 <- telViewUpTo' (-1) ((NotHidden /=) . getHiding) t
    case ignoreSharing $ unEl t0 of
      Def d vs -> do
        res <- isDataOrRecordType d
        case res of
          Nothing -> return (v, t)
          Just{}  -> do
            (args, t1) <- implicitArgs (-1) (NotHidden /=) t
            return (v `apply` args, t1)
      _ -> return (v, t)

---------------------------------------------------------------------------
-- * Let bindings
---------------------------------------------------------------------------

checkLetBindings :: [A.LetBinding] -> TCM a -> TCM a
checkLetBindings = foldr (.) id . map checkLetBinding

checkLetBinding :: A.LetBinding -> TCM a -> TCM a

checkLetBinding b@(A.LetBind i info x t e) ret =
  traceCallCPS_ (CheckLetBinding b) ret $ \ret -> do
    t <- isType_ t
    v <- applyRelevanceToContext (getRelevance info) $ checkDontExpandLast e t
    addLetBinding info x v t ret

checkLetBinding b@(A.LetPatBind i p e) ret =
  traceCallCPS_ (CheckLetBinding b) ret $ \ret -> do
    p <- expandPatternSynonyms p
    (v, t) <- inferExpr' ExpandLast e
    let -- construct a type  t -> dummy  for use in checkLeftHandSide
        t0 = El (getSort t) $ Pi (Dom defaultArgInfo t) (NoAbs underscore typeDontCare)
        p0 = Arg defaultArgInfo (Named Nothing p)
    reportSDoc "tc.term.let.pattern" 10 $ vcat
      [ text "let-binding pattern p at type t"
      , nest 2 $ vcat
        [ text "p (A) =" <+> text (show p) -- prettyTCM p
        , text "t     =" <+> prettyTCM t
        ]
      ]
    fvs <- getContextSize
    checkLeftHandSide (CheckPattern p EmptyTel t) Nothing [p0] t0 Nothing $ \ (LHSResult _ delta0 ps _t _ asb) -> bindAsPatterns asb $ do
          -- After dropping the free variable patterns there should be a single pattern left.
      let p = case drop fvs ps of [p] -> namedArg p; _ -> __IMPOSSIBLE__
          -- Also strip the context variables from the telescope
          delta = telFromList $ drop fvs $ telToList delta0
      reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
        [ text "p (I) =" <+> text (show p)
        , text "delta =" <+> text (show delta)
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
          sigma = zipWith ($) fs (repeat v)
          -- We apply the types of the let bound-variables to this substitution.
          -- The 0th variable in a context is the last one, so we reverse.
          -- Further, we need to lower all other de Bruijn indices by
          -- the size of delta, so we append the identity substitution.
          sub    = parallelS (reverse sigma)

          -- Outer let-bindings will have been rebound by checkLeftHandSide, so
          -- we need to strenghten those as well. Don't use a strengthening
          -- subsititution since @-patterns in the pattern binding will reference
          -- the pattern variables.
          subLetBind (OpenThing cxt va) = OpenThing (drop toDrop cxt) (applySubst sub va)
      escapeContext toDrop $ updateModuleParameters sub
                           $ locally eLetBindings (fmap subLetBind) $ do
        reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
          [ text "delta =" <+> prettyTCM delta
          , text "binds =" <+> text (show binds) -- prettyTCM binds
          ]
{- WE CANNOT USE THIS BINDING
       -- We add a first let-binding for the value of e.
       x <- freshNoName (getRange e)
       addLetBinding Relevant x v t $ do
 -}
        let fdelta = flattenTel delta
        reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
          [ text "fdelta =" <+> text (show fdelta)
          ]
        let tsl  = applySubst sub fdelta
        -- We get a list of types
        let ts   = map unDom tsl
        -- and relevances.
        let infos = map domInfo tsl
        -- We get list of names of the let-bound vars from the context.
        let xs   = map (fst . unDom) (reverse binds)
        -- We add all the bindings to the context.
        foldr (uncurry4 addLetBinding) ret $ zip4 infos xs sigma ts

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
    [ text "context =" <+> (prettyTCM =<< getContextTelescope)
    , text "module  =" <+> (prettyTCM =<< currentModule)
    , text "fv      =" <+> (text $ show fv)
    ]
  checkSectionApplication i x modapp copyInfo
  withAnonymousModule x new ret
-- LetOpen and LetDeclaredVariable are only used for highlighting.
checkLetBinding A.LetOpen{} ret = ret
checkLetBinding (A.LetDeclaredVariable _) ret = ret
