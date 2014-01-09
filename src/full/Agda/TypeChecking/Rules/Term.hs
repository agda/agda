{-# LANGUAGE CPP, PatternGuards, TupleSections, NamedFieldPuns,
      MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}

module Agda.TypeChecking.Rules.Term where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Error
import Data.Maybe
import Data.List hiding (sort)
import qualified Data.Map as Map
import Data.Traversable (sequenceA)

import Agda.Interaction.Options

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Concrete.Pretty () -- only Pretty instances
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Scope.Base (emptyScopeInfo)
import Agda.Syntax.Translation.InternalToAbstract (reify)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Quote
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Level
import Agda.TypeChecking.Rules.LHS (checkLeftHandSide)

import Agda.Utils.Fresh
import Agda.Utils.Tuple
import Agda.Utils.Permutation
import Agda.Utils.List (zipWithTails)

import {-# SOURCE #-} Agda.TypeChecking.Empty (isEmptyType)
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl (checkSectionApplication)
import {-# SOURCE #-} Agda.TypeChecking.Rules.Def (checkFunDef,checkFunDef')

import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size

#include "../../undefined.h"
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
  traceCall (IsType_ e) $ sharedType <$>
  case unScope e of
    A.Fun i (Arg info t) b -> do
      a <- Dom info <$> isType_ t
      b <- isType_ b
      return $ El (sLub (getSort $ unDom a) (getSort b)) (Pi (convColor a) (NoAbs "_" b))
    A.Pi _ tel e -> do
      checkTelescope_ tel $ \tel -> do
        t   <- instantiateFull =<< isType_ e
        tel <- instantiateFull tel
        return $ telePi tel t
    A.Set _ n    -> do
      n <- ifM typeInType (return 0) (return n)
      return $ sort (mkType n)
    A.App i s (Arg (ArgInfo NotHidden r cs) l)
      | A.Set _ 0 <- unScope s ->
      ifNotM hasUniversePolymorphism
          (typeError $ GenericError "Use --universe-polymorphism to enable level arguments to Set")
      $ {- else -} do
        lvl <- levelType
        -- allow NonStrict variables when checking level
        --   Set : (NonStrict) Level -> Set\omega
        n   <- levelView =<< do
          applyRelevanceToContext NonStrict $
            checkExpr (namedThing l) lvl
        return $ sort (Type n)
    _ -> do
      s <- workOnTypes $ newSortMeta
      isType e s

-- | Check that an expression is a type which is equal to a given type.
isTypeEqualTo :: A.Expr -> Type -> TCM Type
isTypeEqualTo e t = case e of
  A.ScopedExpr _ e -> isTypeEqualTo e t
  A.Underscore i | A.metaNumber i == Nothing -> return t
  e -> workOnTypes $ do
    t' <- isType e (getSort t)
    t' <$ leqType t t'

leqType_ :: Type -> Type -> TCM ()
leqType_ t t' = workOnTypes $ leqType t t'

{- UNUSED
-- | Force a type to be a Pi. Instantiates if necessary. The 'Hiding' is only
--   used when instantiating a meta variable.

forcePi :: Hiding -> String -> Type -> TCM (Type, Constraints)
forcePi h name (El s t) =
    do	t' <- reduce t
	case t' of
	    Pi _ _	-> return (El s t', [])
            _           -> do
                sa <- newSortMeta
                sb <- newSortMeta
                let s' = sLub sa sb

                a <- newTypeMeta sa
                x <- freshName_ name
		let arg = Arg h Relevant a
                b <- addCtx x arg $ newTypeMeta sb
                let ty = El s' $ Pi arg (Abs (show x) b)
                cs <- equalType (El s t') ty
                ty' <- reduce ty
                return (ty', cs)
-}

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

-- | Type check a telescope. Binds the variables defined by the telescope.
checkTelescope_ :: A.Telescope -> (Telescope -> TCM a) -> TCM a
checkTelescope_ [] ret = ret EmptyTel
checkTelescope_ (b : tel) ret =
    checkTypedBindings_ b $ \tel1 ->
    checkTelescope_ tel   $ \tel2 ->
	ret $ abstract tel1 tel2

-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
checkTypedBindings_ :: A.TypedBindings -> (Telescope -> TCM a) -> TCM a
checkTypedBindings_ = checkTypedBindings PiNotLam

data LamOrPi = LamNotPi | PiNotLam deriving (Eq,Show)

-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
--
--   Parametrized by a flag wether we check a typed lambda or a Pi. This flag
--   is needed for irrelevance.
checkTypedBindings :: LamOrPi -> A.TypedBindings -> (Telescope -> TCM a) -> TCM a
checkTypedBindings lamOrPi (A.TypedBindings i (Arg info b)) ret =
    checkTypedBinding lamOrPi info b $ \ bs ->
    ret $ telFromList bs

checkTypedBinding :: LamOrPi -> A.ArgInfo -> A.TypedBinding -> (ListTel -> TCM a) -> TCM a
checkTypedBinding lamOrPi info (A.TBind i xs e) ret = do
    -- Andreas, 2011-04-26 irrelevant function arguments may appear
    -- non-strictly in the codomain type
    -- 2011-10-04 if flag --experimental-irrelevance is set
    allowed <- optExperimentalIrrelevance <$> pragmaOptions
    t <- modEnv lamOrPi allowed $ isType_ e
    let info' = mapRelevance (modRel lamOrPi allowed) info
    addCtxs xs (convColor $ Dom info' t) $ ret $ bindsToTel xs (convColor $ Dom info t)
    where
        -- if we are checking a typed lambda, we resurrect before we check the
        -- types, but do not modify the new context entries
        -- otherwise, if we are checking a pi, we do not resurrect, but
        -- modify the new context entries
        modEnv LamNotPi True = doWorkOnTypes
        modEnv _        _    = id
        modRel PiNotLam True = irrToNonStrict
        modRel _        _    = id
checkTypedBinding lamOrPi info (A.TLet _ lbs) ret = do
    checkLetBindings lbs (ret [])

---------------------------------------------------------------------------
-- * Lambda abstractions
---------------------------------------------------------------------------

-- | Type check a lambda expression.
checkLambda :: I.Arg A.TypedBinding -> A.Expr -> Type -> TCM Term
checkLambda (Arg _ (A.TLet _ lbs)) body target =
  checkLetBindings lbs (checkExpr body target)
checkLambda (Arg info (A.TBind _ xs typ)) body target = do
  let numbinds = length xs
  TelV tel btyp <- telViewUpTo numbinds target
  if size tel < size xs || numbinds /= 1
    then dontUseTargetType
    else useTargetType tel btyp
  where
    dontUseTargetType = do
      -- Checking λ (xs : argsT) → body : target
      verboseS "tc.term.lambda" 5 $ tick "lambda-no-target-type"

      -- First check that argsT is a valid type
      argsT <- workOnTypes $ Dom info <$> isType_ typ

      -- In order to have as much type information as possible when checking
      -- body, we first unify (xs : argsT) → ?t₁ with the target type. If this
      -- is inconclusive we need to block the resulting term so we create a
      -- fresh problem for the check.
      t1 <- addCtxs xs argsT $ workOnTypes newTypeMeta_
      let tel = telFromList $ bindsToTel xs argsT
      -- Do not coerce hidden lambdas
      if (getHiding info /= NotHidden) then do
        pid <- newProblem_ $ leqType (telePi tel t1) target
        -- Now check body : ?t₁
        v <- addCtxs xs argsT $ checkExpr body t1
        -- Block on the type comparison
        blockTermOnProblem target (teleLam tel v) pid
       else do
        -- Now check body : ?t₁
        v <- addCtxs xs argsT $ checkExpr body t1
        -- Block on the type comparison
        coerce (teleLam tel v) (telePi tel t1) target

    useTargetType tel@(ExtendTel arg (Abs y EmptyTel)) btyp = do
        verboseS "tc.term.lambda" 5 $ tick "lambda-with-target-type"
        unless (getHiding arg == getHiding info) $ typeError $ WrongHidingInLambda target
        -- Andreas, 2011-10-01 ignore relevance in lambda if not explicitly given
        let r  = getRelevance info
            r' = getRelevance arg -- relevance of function type
        when (r == Irrelevant && r' /= r) $ typeError $ WrongIrrelevanceInLambda target
--        unless (getRelevance arg == r) $ typeError $ WrongIrrelevanceInLambda target
        -- We only need to block the final term on the argument type
        -- comparison. The body will be blocked if necessary. We still want to
        -- compare the argument types first, so we spawn a new problem for that
        -- check.
        (pid, argT) <- newProblem $ isTypeEqualTo typ (unDom arg)
        v <- add y (Dom (setRelevance r' info) argT) $ checkExpr body btyp
        blockTermOnProblem target (Lam info $ Abs (show xc) v) pid
      where
        [x] = xs
        xc  = nameConcrete x
        add y | C.isNoName xc = addCtxString y
              | otherwise     = addCtx x
    useTargetType _ _ = __IMPOSSIBLE__

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
--          return $ Lam info' absurdBody
          -- Add helper function
          top <- currentModule
          aux <- qualify top <$> freshName (getRange i) absurdLambdaName
          -- if we are in irrelevant position, the helper function
          -- is added as irrelevant
          rel <- asks envRelevance
          reportSDoc "tc.term.absurd" 10 $ vcat
            [ text "Adding absurd function" <+> prettyTCM rel <> prettyTCM aux
            , nest 2 $ text "of type" <+> prettyTCM t'
            ]
          addConstant aux
            $ Defn (setRelevance rel info') aux t'
                   [Nonvariant] [Unused] (defaultDisplayForm aux)
                   0 noCompiledRep
            $ Function
              { funClauses        =
                  [Clause
                    { clauseRange     = getRange e
                    , clauseTel       = EmptyTel   -- telFromList [fmap ("()",) dom]
                    , clausePerm      = Perm 1 []  -- Perm 1 [0]
                    , namedClausePats = [Arg info' $ Named (Just $ absName b) $ VarP "()"]
                    , clauseBody      = Bind $ NoAbs "()" NoBody
                    , clauseType      = Just $ setRelevance rel $ defaultArg $ absBody b
                    }
                  ]
              , funCompiled       = Just Fail
              , funDelayed        = NotDelayed
              , funInv            = NotInjective
              , funAbstr          = ConcreteDef
              , funMutual         = []
              , funProjection     = Nothing
              , funStatic         = False
              , funCopy           = False
              , funTerminates     = Just True
              , funExtLam         = Nothing
              , funWith           = Nothing
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
   t <- instantiateFull t
   ifBlockedType t (\ m t' -> postponeTypeCheckingProblem_ $ CheckExpr e t') $ \ t -> do
     j   <- currentOrFreshMutualBlock
     rel <- asks envRelevance
     let info = setRelevance rel defaultArgInfo
     -- Andreas, 2013-12-28: add extendedlambda as @Function@, not as @Axiom@;
     -- otherwise, @addClause@ in @checkFunDef'@ fails (see issue 1009).
     addConstant qname $
       (defaultDefn info qname t emptyFunction) { defMutual = j }
     reportSDoc "tc.term.exlam" 50 $
       text "extended lambda's implementation \"" <> prettyTCM qname <>
       text "\" has type: " $$ prettyTCM t -- <+> text " where clauses: " <+> text (show cs)
     args     <- getContextArgs
     top      <- currentModule
     freevars <- getModuleFreeVars top
     -- freevars <- getSecFreeVars top --Andreas, 2013-02-26 this could be wrong in the presence of module parameters and a where block
     let argsNoParam = genericDrop freevars args -- don't count module parameters
     let (hid, notHid) = partition isHidden argsNoParam
     abstract (A.defAbstract di) $ checkFunDef' t info NotDelayed
                                                (Just (length hid, length notHid)) Nothing di qname cs
     reduce $ (Def qname [] `apply` args)
  where
    -- Concrete definitions cannot use information about abstract things.
    abstract ConcreteDef = inConcreteMode
    abstract AbstractDef = inAbstractMode

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

-- | @checkRecordExpression fs e t@ checks record construction against type @t@.
-- Precondition @e = Rec _ fs@.
checkRecordExpression :: A.Assigns -> A.Expr -> Type -> TCM Term
checkRecordExpression fs e t = do
  reportSDoc "tc.term.rec" 10 $ sep
    [ text "checking record expression"
    , prettyA e
    ]
  t <- reduce t
  case ignoreSharing $ unEl t of
    Def r es  -> do
      let ~(Just vs) = allApplyElims es
      reportSDoc "tc.term.rec" 20 $ text $ "  r   = " ++ show r
{-
      axs    <- getRecordFieldNames r
      let xs = map unArg axs
      reportSDoc "tc.term.rec" 20 $ text $ "  xs  = " ++ show xs
      ftel   <- getRecordFieldTypes r
      reportSDoc "tc.term.rec" 20 $ text   "  ftel= " <> prettyTCM ftel
      con    <- getRecordConstructor r
      reportSDoc "tc.term.rec" 20 $ text $ "  con = " ++ show con
-}
      def <- getRecordDef r
      let axs  = recordFieldNames def
          xs   = map unArg axs
          ftel = recTel def
          con  = killRange $ recConHead def
      reportSDoc "tc.term.rec" 20 $ vcat
        [ text $ "  xs  = " ++ show xs
        , text   "  ftel= " <> prettyTCM ftel
        , text $ "  con = " ++ show con
        ]
      scope  <- getScope
      let arg x e =
            case [ a | a <- axs, unArg a == x ] of
              [a] -> unnamed e <$ a
              _   -> defaultNamedArg e -- we only end up here if the field names are bad
      let meta x = A.Underscore $ A.MetaInfo (getRange e) scope Nothing (show x)
          missingExplicits = [ (unArg a, [unnamed . meta <$> a])
                             | a <- axs, notHidden a
                             , notElem (unArg a) (map fst fs) ]
      -- In es omitted explicit fields are replaced by underscores
      -- (from missingExplicits). Omitted implicit or instance fields
      -- are still left out and inserted later by checkArguments_.
      es   <- concat <$> orderFields r [] xs ([ (x, [arg x e]) | (x, e) <- fs ] ++
                                              missingExplicits)
      let tel = ftel `apply` vs
      args <- checkArguments_ ExpandLast (getRange e)
                es -- (zipWith (\ax e -> fmap (const (unnamed e)) ax) axs es)
                tel
      -- Don't need to block here!
      reportSDoc "tc.term.rec" 20 $ text $ "finished record expression"
      return $ Con con args
    MetaV _ _ -> do
      let fields = map fst fs
      rs <- findPossibleRecords fields
      case rs of
          -- If there are no records with the right fields we might as well fail right away.
        [] -> case fs of
          []       -> typeError $ GenericError "There are no records in scope"
          [(f, _)] -> typeError $ GenericError $ "There is no known record with the field " ++ show f
          _        -> typeError $ GenericError $ "There is no known record with the fields " ++ unwords (map show fields)
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
    _         -> typeError $ ShouldBeRecordType t


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
        es <- orderFields r Nothing xs $ map (\(x, e) -> (x, Just e)) fs
        let es' = zipWith (replaceFields name ei) projs es
        checkExpr (A.Rec ei [ (x, e) | (x, Just e) <- zip xs es' ]) t
    MetaV _ _ -> do
      inferred <- inferExpr recexpr >>= reduce . snd
      case ignoreSharing $ unEl inferred of
        MetaV _ _ -> postponeTypeCheckingProblem_ $ CheckExpr e t
        _         -> do
          v <- checkExpr e inferred
          coerce v inferred t
    _         -> typeError $ ShouldBeRecordType t
  where
    replaceFields :: Name -> A.ExprInfo -> I.Arg A.QName -> Maybe A.Expr -> Maybe A.Expr
    replaceFields n ei a@(Arg _ p) Nothing | notHidden a =
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

-- moved to TypeChecking.Monad.Builtin to avoid import cycles:
-- litType :: Literal -> TCM Type

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

{- MOVED to TC.Datatypes.getConForm
-- TODO: move somewhere suitable
reduceCon :: QName -> TCM ConHead
reduceCon x = do
  Con c [] <- ignoreSharing <$> (constructorForm =<< getConHead c)
  return c
-}

-- | @checkArguments' exph r args t0 t k@ tries @checkArguments exph args t0 t@.
-- If it succeeds, it continues @k@ with the returned results.  If it fails,
-- it registers a postponed typechecking problem and returns the resulting new
-- meta variable.
--
-- Checks @e := ((_ : t0) args) : t@.
checkArguments' ::
  ExpandHidden -> ExpandInstances -> Range -> [I.NamedArg A.Expr] -> Type -> Type ->
  (Args -> Type -> TCM Term) -> TCM Term
checkArguments' exph expIFS r args t0 t k = do
  z <- runErrorT $ checkArguments exph expIFS r args t0 t
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
      postponeTypeCheckingProblem_ (CheckArgs exph expIFS r es t0 t $ \vs t -> k (us ++ vs) t)
      -- if unsuccessful, postpone checking until t0 unblocks

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t0 =
  verboseBracket "tc.term.expr.top" 5 "checkExpr" $
  traceCall (CheckExprCall e t0) $ localScope $ doExpandLast $ shared <$> do
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

    let scopedExpr (A.ScopedExpr scope e) = setScope scope >> scopedExpr e
	scopedExpr e			  = return e

    e <- scopedExpr e

    case e of

	A.ScopedExpr scope e -> __IMPOSSIBLE__ -- setScope scope >> checkExpr e t

	-- Insert hidden lambda if appropriate
	_   | Pi (Dom info _) _ <- ignoreSharing $ unEl t
            , not (hiddenLambdaOrHole (getHiding info) e)
            , getHiding info /= NotHidden -> do
		x <- freshName r (argName t)
                info <- reify info
                reportSLn "tc.term.expr.impl" 15 $ "Inserting implicit lambda"
		checkExpr (A.Lam (A.ExprRange $ getRange e) (domainFree info x) e) t
	    where
		r = case rStart $ getRange e of
                      Nothing  -> noRange
                      Just pos -> posToRange pos pos

                hiddenLambdaOrHole h (A.AbsurdLam _ h') | h == h'                      = True
                hiddenLambdaOrHole h (A.ExtendedLam _ _ _ [])                          = False
                hiddenLambdaOrHole h (A.ExtendedLam _ _ _ cls)                         = any hiddenLHS cls
		hiddenLambdaOrHole h (A.Lam _ (A.DomainFree info' _) _) | h == getHiding info'       = True
		hiddenLambdaOrHole h (A.Lam _ (A.DomainFull (A.TypedBindings _ (Arg info' _))) _)
                  | h == getHiding info'                                                            = True
		hiddenLambdaOrHole _ (A.QuestionMark _)				       = True
		hiddenLambdaOrHole _ _						       = False

                hiddenLHS (A.Clause (A.LHS _ (A.LHSHead _ (a : _)) _) _ _) = elem (getHiding a) [Hidden, Instance]
                hiddenLHS _ = False

        -- a meta variable without arguments: type check directly for efficiency
	A.QuestionMark i -> checkMeta newQuestionMark t0 i -- Andreas, 2013-05-22 use unreduced type t0!
	A.Underscore i   -> checkMeta (newValueMeta RunMetaOccursCheck) t0 i

	A.WithApp _ e es -> typeError $ NotImplemented "type checking of with application"

        -- check |- Set l : t  (requires universe polymorphism)
        A.App i s (Arg ai l)
          | A.Set _ 0 <- unScope s, visible ai ->
          ifNotM hasUniversePolymorphism
              (typeError $ GenericError "Use --universe-polymorphism to enable level arguments to Set")
          $ {- else -} do
            lvl <- levelType
            -- allow NonStrict variables when checking level
            --   Set : (NonStrict) Level -> Set\omega
            n   <- levelView =<< do
              applyRelevanceToContext NonStrict $
                checkExpr (namedThing l) lvl
            -- check that Set (l+1) <= t
            reportSDoc "tc.univ.poly" 10 $
              text "checking Set " <+> prettyTCM n <+>
              text "against" <+> prettyTCM t
            coerce (Sort $ Type n) (sort $ sSuc $ Type n) t

        A.App i q (Arg ai e)
          | A.Quote _ <- unScope q, visible ai -> do
          let quoted (A.Def x) = return x
              quoted (A.Con (AmbQ [x])) = return x
              quoted (A.Con (AmbQ xs))  = typeError $ GenericError $ "quote: Ambigous name: " ++ show xs
              quoted (A.ScopedExpr _ e) = quoted e
              quoted _                  = typeError $ GenericError $ "quote: not a defined name"
          x <- quoted (namedThing e)
          ty <- qNameType
          coerce (quoteName x) ty t

          | A.QuoteTerm _ <- unScope q ->
             do (et, _) <- inferExpr (namedThing e)
                q <- quoteTerm =<< normalise et
                ty <- el primAgdaTerm
                coerce q ty t

	  | A.Unquote _ <- unScope q ->
	     do e1 <- checkExpr (namedThing e) =<< el primAgdaTerm
	        e2 <- unquote e1
                checkTerm e2 t
        A.Quote _ -> typeError $ GenericError "quote must be applied to a defined name"
        A.QuoteTerm _ -> typeError $ GenericError "quoteTerm must be applied to a term"
        A.Unquote _ -> typeError $ GenericError "unquote must be applied to a term"

        A.AbsurdLam i h -> checkAbsurdLambda i h e t

        A.ExtendedLam i di qname cs -> checkExtendedLambda i di qname cs e t

	A.Lam i (A.DomainFull (A.TypedBindings _ b)) e -> checkLambda (convColor b) e t

	A.Lam i (A.DomainFree info x) e0 -> checkExpr (A.Lam i (domainFree info x) e0) t

	A.Lit lit    -> checkLiteral lit t
	A.Let i ds e -> checkLetBindings ds $ checkExpr e t
	A.Pi _ tel e -> do
	    t' <- checkTelescope_ tel $ \tel -> do
                    t   <- instantiateFull =<< isType_ e
                    tel <- instantiateFull tel
                    return $ telePi tel t
            let s = getSort t'
            when (s == Inf) $ reportSDoc "tc.term.sort" 20 $
              vcat [ text ("reduced to omega:")
                   , nest 2 $ text "t   =" <+> prettyTCM t'
                   , nest 2 $ text "cxt =" <+> (prettyTCM =<< getContextTelescope)
                   ]
	    coerce (unEl t') (sort s) t
	A.Fun _ (Arg info a) b -> do
	    a' <- isType_ a
	    b' <- isType_ b
	    s <- reduce $ getSort a' `sLub` getSort b'
	    coerce (Pi (convColor $ Dom info a') (NoAbs "_" b')) (sort s) t
	A.Set _ n    -> do
          n <- ifM typeInType (return 0) (return n)
	  coerce (Sort $ mkType n) (sort $ mkType $ n + 1) t
	A.Prop _     -> do
          typeError $ GenericError "Prop is no longer supported"
          -- s <- ifM typeInType (return $ mkType 0) (return Prop)
	  -- coerce (Sort Prop) (sort $ mkType 1) t

	A.Rec _ fs  -> checkRecordExpression fs e t

        A.RecUpdate ei recexpr fs -> checkRecordUpdate ei recexpr fs e t

	A.DontCare e -> -- resurrect vars
          ifM ((Irrelevant ==) <$> asks envRelevance)
            (dontCare <$> do applyRelevanceToContext Irrelevant $ checkExpr e t)
            (internalError "DontCare may only appear in irrelevant contexts")

        e0@(A.QuoteGoal _ x e) -> do
          t' <- etaContract =<< normalise t
          let metas = allMetas t'
          case metas of
            _:_ -> postponeTypeCheckingProblem (CheckExpr e0 t') $ andM $ map isInstantiatedMeta metas
            []  -> do
              quoted <- quoteTerm (unEl t')
              tmType <- agdaTermType
              (v, ty) <- addLetBinding defaultArgInfo x quoted tmType (inferExpr e)
              blockTerm t' $ coerce v ty t'

        A.ETel _   -> __IMPOSSIBLE__

	-- Application
        _   | Application hd args <- appView e -> checkApplication hd args e t

-- | @checkApplication hd args e t@ checks an application.
--   Precondition: @Application hs args = appView e@
--
--   @checkApplication@ disambiguates constructors
--   (and continues to 'checkConstructorApplication')
--   and resolves pattern synonyms.
checkApplication :: A.Expr -> A.Args -> A.Expr -> Type -> TCM Term
checkApplication hd args e t = do
  case hd of

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
{-
      cs  <- zip cs . zipWith setRange (map getRange cs) <$> mapM reduceCon cs
      reportSLn "tc.check.term" 40 $ "  ranges after: " ++ show (getRange cs)
      reportSLn "tc.check.term" 40 $ "  reduced: " ++ show cs
      dcs <- mapM (\(c0, c1) -> (getData /\ const c0) . theDef <$> getConstInfo c1) cs
-}
      -- Type error
      let badCon t = typeError $ DoesNotConstructAnElementOf (head cs) t
--      let badCon t = typeError $ DoesNotConstructAnElementOf (fst $ head cs) t

      -- Lets look at the target type at this point
      let getCon = do
          TelV tel t1 <- telView t
          addCtxTel tel $ do
           reportSDoc "tc.check.term.con" 40 $ nest 2 $
             text "target type: " <+> prettyTCM t1
           ifBlockedType t1 (\ m t -> return Nothing) $ \ t' ->
             (isDataOrRecord (unEl t') >>=) $ maybe (badCon t') $ \ d ->
               case [ c | (d', c) <- dcs, d == d' ] of
                 [c] -> do
                   reportSLn "tc.check.term" 40 $ "  decided on: " ++ show c
                   return $ Just c
                 []  -> badCon $ t' $> Def d []
                 cs  -> typeError $ CantResolveOverloadedConstructorsTargetingSameDatatype d $ map conName cs
      let unblock = isJust <$> getCon -- to unblock, call getCon later again
      mc <- getCon
      case mc of
        Just c  -> checkConstructorApplication e t c $ map convColor args
        Nothing -> postponeTypeCheckingProblem (CheckExpr e t) unblock

    -- Subcase: non-ambiguous constructor
    (A.Con (AmbQ [c])) -> do
      -- augment c with record fields, but do not revert to original name
      con <- getOrigConHead c
--      con <- setConName c . conSrcCon . theDef <$> getConstInfo c
      checkConstructorApplication e t con $ map convColor args

    -- Subcase: pattern synonym
    (A.PatternSyn n) -> do
      (ns, p) <- lookupPatternSyn n
      -- Expand the pattern synonym by substituting for
      -- the arguments we have got and lambda-lifting
      -- over the ones we haven't.
      let (zs, ns', as) = zipWithTails (\n a -> (n, namedThing (unArg a))) ns args
          p'            = A.patternToExpr $ setRange (getRange n) p
          e'            = A.lambdaLiftExpr ns' (A.substExpr zs p') `A.app` as
      checkExpr e' t

    -- Subcase: defined symbol or variable.
    _ -> checkHeadApplication e t hd $ map convColor args

-- | Turn a domain-free binding (e.g. lambda) into a domain-full one,
--   by inserting an underscore for the missing type.
domainFree :: A.ArgInfo -> A.Name -> A.LamBinding
domainFree info x =
  A.DomainFull $ A.TypedBindings r $ Arg info $ A.TBind r [x] $ A.Underscore underscoreInfo
  where
    r = getRange x
    underscoreInfo = A.MetaInfo
      { A.metaRange          = r
      , A.metaScope          = emptyScopeInfo
      , A.metaNumber         = Nothing
      , A.metaNameSuggestion = show x
      }

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

checkMeta :: (Type -> TCM Term) -> Type -> A.MetaInfo -> TCM Term
checkMeta newMeta t i = fst <$> checkOrInferMeta newMeta (Just t) i
{-
checkMeta newMeta t i = do
  case A.metaNumber i of
    Nothing -> do
      setScope (A.metaScope i)
      v <- newMeta t
      setValueMetaName v (A.metaNameSuggestion i)
      return v
    -- Rechecking an existing metavariable
    Just n -> do
      let v = MetaV (MetaId n) []
      t' <- jMetaType . mvJudgement <$> lookupMeta (MetaId n)
      coerce v t' t
-}

inferMeta :: (Type -> TCM Term) -> A.MetaInfo -> TCM (Args -> Term, Type)
inferMeta newMeta i = mapFst apply <$> checkOrInferMeta newMeta Nothing i
{-
inferMeta newMeta i =
  case A.metaNumber i of
    Nothing -> do
      setScope (A.metaScope i)
      t <- workOnTypes $ newTypeMeta_
      v <- newMeta t
      return (apply v, t)
    -- Rechecking an existing metavariable
    Just n -> do
      let v = MetaV (MetaId n)
      t' <- jMetaType . mvJudgement <$> lookupMeta (MetaId n)
      return (v, t')
-}

-- | Type check a meta variable.
--   If its type is not given, we return its type, or a fresh one, if it is a new meta.
--   If its type is given, we check that the meta has this type, and we return the same
--   type.
checkOrInferMeta :: (Type -> TCM Term) -> Maybe Type -> A.MetaInfo -> TCM (Term, Type)
checkOrInferMeta newMeta mt i = do
  case A.metaNumber i of
    Nothing -> do
      setScope (A.metaScope i)
      t <- maybe (workOnTypes $ newTypeMeta_) return mt
      v <- newMeta t
      setValueMetaName v (A.metaNameSuggestion i)
      return (v, t)
    -- Rechecking an existing metavariable
    Just n -> do
      let v = MetaV (MetaId n) []
      t' <- jMetaType . mvJudgement <$> lookupMeta (MetaId n)
      case mt of
        Nothing -> return (v, t')
        Just t  -> (,t) <$> coerce v t' t

---------------------------------------------------------------------------
-- * Applications
---------------------------------------------------------------------------

-- | Infer the type of a head thing (variable, function symbol, or constructor).
--   We return a function that applies the head to arguments.
--   This is because in case of a constructor we want to drop the parameters.
inferHead :: A.Expr -> TCM (Args -> Term, Type)
inferHead e = do
  case e of
    (A.Var x) -> do -- traceCall (InferVar x) $ do
      (u, a) <- getVarInfo x
      when (unusableRelevance $ getRelevance a) $
        typeError $ VariableIsIrrelevant x
      return (apply u, unDom a)
    (A.Def x) -> do
      proj <- isProjection x
      case proj of
        Nothing -> do
          (u, a) <- inferDef (\ f args -> return $ Def f $ map Apply args) x
          return (apply u, a)
        Just Projection{ projDropPars = proj } -> do
{- MOVED to Rules/Record.hs and ProjectionLike.hs
        Just Projection{ projIndex = n, projProper, projDropPars = proj } -> do
          reportSDoc "tc.term.proj" 10 $ sep
            [ text "building projection" <+> prettyTCM x
            , nest 2 $ parens (text "ctx =" <+> (text . show =<< do
                size <$> freeVarsToApply x))
            , nest 2 $ parens (text "n =" <+> text (show n))
            , nest 2 $ parens (text "m =" <+> (text . show =<< getDefFreeVars x))
            ]
          let is | n == 0    = __IMPOSSIBLE__
                 | otherwise = genericReplicate (n - 1) defaultArgInfo -- TODO: hiding
              names = [ s ++ [c] | s <- "" : names, c <- ['a'..'z'] ]
              -- Andreas, 2013-10-19
              -- proper projections are postfix, projection-like defs are prefix
              core | projProper = (Lam defaultArgInfo $ Abs "r" $ Var 0 [Proj x])
                   | otherwise  = Def x []
              -- leading lambdas are to ignore parameter applications
              proj  = foldr (\ (i, s) -> Lam i . NoAbs s) core (zip is names)
-}
          (u, a) <- inferDef (\ f vs -> return $ proj `apply` vs) x
          return (apply u, a)
    (A.Con (AmbQ [c])) -> do

      -- Constructors are polymorphic internally.
      -- So, when building the constructor term
      -- we should throw away arguments corresponding to parameters.

      -- First, inferDef will try to apply the constructor
      -- to the free parameters of the current context. We ignore that.
      (u, a) <- inferDef (\ c _ -> getOrigConTerm c) c

      -- Next get the number of parameters in the current context.
      Constructor{conPars = n} <- theDef <$> (instantiateDef =<< getConstInfo c)

      reportSLn "tc.term.con" 7 $ unwords [show c, "has", show n, "parameters."]

      -- So when applying the constructor throw away the parameters.
      return (apply u . genericDrop n, a)
    (A.Con _) -> __IMPOSSIBLE__  -- inferHead will only be called on unambiguous constructors
    (A.QuestionMark i) -> inferMeta newQuestionMark i
    (A.Underscore i)   -> inferMeta (newValueMeta RunMetaOccursCheck) i
    e -> do
      (term, t) <- inferExpr e
      return (apply term, t)

inferDef :: (QName -> Args -> TCM Term) -> QName -> TCM (Term, Type)
inferDef mkTerm x =
    traceCall (InferDef (getRange x) x) $ do
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
    v  <- mkTerm x vs
    reportSDoc "tc.term.def" 10 $ nest 2 $ text " --> " <+> prettyTCM v
    return (v, t)

-- | Check the type of a constructor application. This is easier than
--   a general application since the implicit arguments can be inserted
--   without looking at the arguments to the constructor.
checkConstructorApplication :: A.Expr -> Type -> ConHead -> [I.NamedArg A.Expr] -> TCM Term
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
    let Constructor{conData = d} = theDef cdef
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
        npars  <- getNumberOfParameters d
        npars' <- getNumberOfParameters d'
        caseMaybe (sequenceA $ List2 (npars, npars')) fallback $ \ (List2 (n,n')) -> do
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
        TelV ptel _ <- telViewUpTo n ctype
        let pnames = map (fst . unDom) $ telToList ptel
        -- drop the parameter arguments
            args' = dropArgs pnames args
        -- check the non-parameter arguments
        expandLast <- asks envExpandLast
        checkArguments' expandLast ExpandInstanceArguments (getRange c) args' ctype' t $ \us t' -> do
          reportSDoc "tc.term.con" 20 $ nest 2 $ vcat
            [ text "us     =" <+> prettyTCM us
            , text "t'     =" <+> prettyTCM t' ]
          coerce (Con c us) t' t
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
      let (hargs, rest) = span isHidden args
          notUnderscore A.Underscore{} = False
          notUnderscore _              = True
      in  any notUnderscore $ map (unScope . namedArg) hargs

    -- Drop the constructor arguments that correspond to parameters.
    dropArgs [] args                                   = args
    dropArgs ps []                                     = args
    dropArgs ps args@(arg : _) | not (isHidden arg) = args
    dropArgs (p:ps) args@(arg : args')
      | (nameOf (unArg arg)) `elem` [Nothing, Just p]  = dropArgs ps args'
      | otherwise                                      = dropArgs ps args


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
          (arg :) *** id $ splitArgs ps args
      | otherwise =
          (dummyUnderscore :) *** id $ splitArgs ps (arg:args)
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
checkHeadApplication :: A.Expr -> Type -> A.Expr -> [I.NamedArg A.Expr] -> TCM Term
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
      checkArguments' expandLast ExpandInstanceArguments (getRange hd) args t0 t $ \vs t1 -> do
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

        reportSDoc "tc.term.con" 10 $ vcat
          [ text "checking" <+>
            prettyTCM fType <+> text "?<=" <+> prettyTCM eType
          ]
        blockTerm t $ f vs <$ workOnTypes (do
          addCtxTel eTel $ leqType fType eType
          compareTel t t1 CmpLeq eTel fTel)

    (A.Def c) | Just c == (nameOfSharp <$> kit) -> do
      -- TODO: Handle coinductive constructors under lets.
      lets <- envLetBindings <$> ask
      unless (Map.null lets) $
        typeError $ NotImplemented
          "coinductive constructor in the scope of a let-bound variable"

      -- The name of the fresh function.
      i <- fresh :: TCM Int
      let name = filter (/= '_') (show $ A.qnameName c) ++ "-" ++ show i
      c' <- setRange (getRange c) <$>
              liftM2 qualify (killRange <$> currentModule)
                             (freshName_ name)

      -- The application of the fresh function to the relevant
      -- arguments.
      e' <- Def c' . map Apply <$> getContextArgs

      -- Add the type signature of the fresh function to the
      -- signature.
      i   <- currentOrFreshMutualBlock
      tel <- getContextTelescope
      -- If we are in irrelevant position, add definition irrelevantly.
      -- TODO: is this sufficient?
      rel <- asks envRelevance
      addConstant c' (Defn (setRelevance rel defaultArgInfo)
                           c' t [] [] (defaultDisplayForm c')
                  i noCompiledRep $ Axiom)

      -- Define and type check the fresh function.
      ctx <- getContext >>= mapM (\d -> flip Dom (unDom d) <$> reify (domInfo d))
      args' <- mapM (\a -> flip Arg (unArg a) <$> reify (argInfo a)) args
      let info   = A.mkDefInfo (A.nameConcrete $ A.qnameName c') defaultFixity'
                               PublicAccess ConcreteDef noRange
          pats   = map (\ (Dom info (n, _)) -> Arg info $ Named Nothing $ A.VarP n) $
                       reverse ctx
          clause = A.Clause (A.LHS (A.LHSRange noRange) (A.LHSHead c' pats) [])
                            (A.RHS $ unAppView (A.Application (A.Con (AmbQ [c])) args'))
                            []

      reportSDoc "tc.term.expr.coind" 15 $ vcat $
          [ text "The coinductive constructor application"
          , nest 2 $ prettyTCM e
          , text "was translated into the application"
          , nest 2 $ prettyTCM e'
          , text "and the function"
          , nest 2 $ prettyTCM rel <> prettyTCM c' <+> text ":"
          , nest 4 $ prettyTCM (telePi tel t)
          , nest 2 $ prettyA clause <> text "."
          ]

      inTopContext $ checkFunDef Delayed info c' [clause]

      reportSDoc "tc.term.expr.coind" 15 $ do
        def <- theDef <$> getConstInfo c'
        text "The definition is" <+> text (show $ funDelayed def) <>
          text "."

      return e'
    A.Con _  -> __IMPOSSIBLE__
    _ -> defaultResult
  where
  defaultResult = do
    (f, t0) <- inferHead hd
    expandLast <- asks envExpandLast
    checkArguments' expandLast ExpandInstanceArguments (getRange hd) args t0 t $ \vs t1 -> do
      coerce (f vs) t1 t
      -- -- try to remove projection redexes  -- fails succeed/Issue286
      -- v <- onlyReduceProjections $ reduce $ f vs
      -- coerce v t1 t

-- Stupid ErrorT!
instance Error (a, b, c) where
  strMsg _ = __IMPOSSIBLE__
  noMsg = __IMPOSSIBLE__

traceCallE :: Error e => (Maybe r -> Call) -> ErrorT e TCM r -> ErrorT e TCM r
traceCallE call m = do
  z <- lift $ traceCall call' $ runErrorT m
  case z of
    Right e  -> return e
    Left err -> throwError err
  where
    call' Nothing          = call Nothing
    call' (Just (Left _))  = call Nothing
    call' (Just (Right x)) = call (Just x)

-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t0'@ and @args : Delta@. Inserts hidden arguments to
--   make this happen.  Returns the evaluated arguments @vs@, the remaining
--   type @t0'@ (which should be a subtype of @t1@) and any constraints @cs@
--   that have to be solved for everything to be well-formed.
--
--   TODO: doesn't do proper blocking of terms
checkArguments :: ExpandHidden -> ExpandInstances -> Range -> [I.NamedArg A.Expr] -> Type -> Type ->
                  ErrorT (Args, [I.NamedArg A.Expr], Type) TCM (Args, Type)

-- Case: no arguments, do not insert trailing hidden arguments: We are done.
checkArguments DontExpandLast _ _ [] t0 t1 = return ([], t0)

-- Case: no arguments, but need to insert trailing hiddens.
checkArguments exh    expandIFS r [] t0 t1 =
    traceCallE (CheckArguments r [] t0 t1) $ lift $ do
      t1' <- unEl <$> reduce t1
      implicitArgs (-1) (expand t1') t0
    where
      expand (Pi (Dom info _) _)   Hidden = getHiding info /= Hidden
      expand _                     Hidden = True
      expand (Pi (Dom info _) _) Instance = getHiding info /= Instance &&
                                            expandIFS == ExpandInstanceArguments
      expand _                   Instance = expandIFS == ExpandInstanceArguments
      expand _                  NotHidden = False

-- Case: argument given.
checkArguments exh expandIFS r args0@(arg@(Arg info e) : args) t0 t1 =
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
          mx = nameOf e        -- name of current argument
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
      ifBlockedType t (\ m t -> throwError ([], args0, t)) $ \ t0' -> do

        -- What can go wrong?

        -- 1. We ran out of function types.
        let shouldBePi
              -- a) It is an explicit argument, but we ran out of function types.
              | notHidden info = lift $ typeError $ ShouldBePi t0'
              -- b) It is an implicit argument, and we did not insert any implicits.
              --    Thus, the type was not a function type to start with.
              | null xs        = lift $ typeError $ ShouldBePi t0'
              -- c) We did insert implicits, but we ran out of implicit function types.
              --    Then, we should inform the user that we did not find his one.
              | otherwise      = lift $ typeError $ WrongNamedArgument arg

        -- 2. We have a function type left, but it is the wrong one.
        --    Our argument must be implicit, case a) is impossible.
        --    (Otherwise we would have ran out of function types instead.)
        let wrongPi info'
              -- b) We have not inserted any implicits.
              | null xs   = lift $ typeError $ WrongHidingInApplication t0'
              -- c) We inserted implicits, but did not find his one.
              | otherwise = lift $ typeError $ WrongNamedArgument arg

        -- (t0', cs) <- forcePi h (name e) t0
        case ignoreSharing $ unEl t0' of
          Pi (Dom info' a) b
            | getHiding info == getHiding info'
              && (notHidden info || maybe True (absName b ==) (nameOf e)) -> do
                u <- lift $ applyRelevanceToContext (getRelevance info') $ do
                  checkExpr (namedThing e) a
                -- save relevance info' from domain in argument
                addCheckedArgs us (Arg info' u) $
                  checkArguments exh expandIFS (fuseRange r e) args (absApp b u) t1
            | otherwise -> wrongPi info'
          _ -> shouldBePi
  where
    addCheckedArgs us u rec =
      (mapFst ((us ++) . (u :)) <$> rec)
        `catchError` \(vs, es, t) ->
          throwError (us ++ u : vs, es, t)

-- | Check that a list of arguments fits a telescope.
checkArguments_ :: ExpandHidden -> Range -> [I.NamedArg A.Expr] -> Telescope -> TCM Args
checkArguments_ exh r args tel = do
    z <- runErrorT $ checkArguments exh ExpandInstanceArguments r args (telePi tel $ sort Prop) (sort Prop)
    case z of
      Right (args, _) -> return args
      Left _          -> __IMPOSSIBLE__


-- | Infer the type of an expression. Implemented by checking against a meta
--   variable.  Except for neutrals, for them a polymorphic type is inferred.
inferExpr :: A.Expr -> TCM (Term, Type)
-- inferExpr e = inferOrCheck e Nothing
inferExpr e = case e of
  _ | Application hd args <- appView e, defOrVar hd -> traceCall (InferExpr e) $ do
    (f, t0) <- inferHead hd
    res <- runErrorT $ checkArguments DontExpandLast ExpandInstanceArguments (getRange hd) (map convColor args) t0 (sort Prop)
    case res of
      Right (vs, t1) -> return (f vs, t1)
      Left t1 -> fallback -- blocked on type t1
  _ -> fallback
  where
    fallback = do
      t <- workOnTypes $ newTypeMeta_
      v <- checkExpr e t
      return (v,t)

defOrVar :: A.Expr -> Bool
defOrVar A.Var{} = True
defOrVar A.Def{} = True
defOrVar (A.ScopedExpr _ e) = defOrVar e
defOrVar _     = False

-- | Used to check aliases @f = e@.
--   Switches off 'ExpandLast' for the checking of top-level application.
checkDontExpandLast :: A.Expr -> Type -> TCM Term
checkDontExpandLast e t = case e of
  _ | Application hd args <- appView e,  defOrVar hd ->
    traceCall (CheckExprCall e t) $ localScope $ dontExpandLast $ shared <$> do
      checkApplication hd args e t
  _ -> checkExpr e t -- note that checkExpr always sets ExpandLast

{- Andreas, 2013-03-15 UNUSED, but don't remove
inferOrCheck :: A.Expr -> Maybe Type -> TCM (Term, Type)
inferOrCheck e mt = case e of
  _ | Application hd args <- appView e, defOrVar hd -> traceCall (InferExpr e) $ do
    (f, t0) <- inferHead hd
    res <- runErrorT $ checkArguments DontExpandLast ExpandInstanceArguments
                                      (getRange hd) (map convColor args) t0 $
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

-- | Infer the type of an expression, and if it is of the form
--   @{tel} -> D vs@ for some datatype @D@ then insert the hidden
--   arguments.  Otherwise, leave the type polymorphic.
inferExprForWith :: A.Expr -> TCM (Term, Type)
inferExprForWith e = do
  (v, t) <- inferExpr e
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

-- TODO: should really use CheckInternal but doesn't quite work at the moment,
-- since CheckInternal can't instantiate metas to sorts or to function types.
checkTerm :: Term -> Type -> TCM Term
checkTerm tm ty = do atm <- withShowAllArguments $ reify tm
                     checkExpr (killRange atm) ty

---------------------------------------------------------------------------
-- * Let bindings
---------------------------------------------------------------------------

checkLetBindings :: [A.LetBinding] -> TCM a -> TCM a
checkLetBindings = foldr (.) id . map checkLetBinding

checkLetBinding :: A.LetBinding -> TCM a -> TCM a

checkLetBinding b@(A.LetBind i info x t e) ret =
  traceCallCPS_ (CheckLetBinding b) ret $ \ret -> do
    t <- isType_ t
    v <- applyRelevanceToContext (getRelevance info) $ checkExpr e t
    addLetBinding (convColor info) x v t ret

checkLetBinding b@(A.LetPatBind i p e) ret =
  traceCallCPS_ (CheckLetBinding b) ret $ \ret -> do
    (v, t) <- inferExpr e
    let -- construct a type  t -> dummy  for use in checkLeftHandSide
        t0 = El (getSort t) $ Pi (Dom defaultArgInfo t) (NoAbs "_" typeDontCare)
        p0 = Arg defaultArgInfo (Named Nothing p)
    reportSDoc "tc.term.let.pattern" 10 $ vcat
      [ text "let-binding pattern p at type t"
      , nest 2 $ vcat
        [ text "p (A) =" <+> text (show p) -- prettyTCM p
        , text "t     =" <+> prettyTCM t
        ]
      ]
    checkLeftHandSide (CheckPattern p EmptyTel t) Nothing [p0] t0 $ \ mgamma delta sub xs ps t' perm -> do
      -- A single pattern in internal syntax is returned.
      let p = case ps of [p] -> namedArg p; _ -> __IMPOSSIBLE__
      reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
        [ text "p (I) =" <+> text (show p)
        , text "delta =" <+> text (show delta)
        ]
      -- We translate it into a list of projections.
      fs <- recordPatternToProjections p
      -- We remove the bindings for the pattern variables from the context.
      cxt0 <- getContext
      let (binds, cxt) = splitAt (size delta) cxt0
      escapeContext (length binds) $ do
        reportSDoc "tc.term.let.pattern" 20 $ nest 2 $ vcat
          [ text "delta =" <+> prettyTCM delta
          , text "binds =" <+> text (show binds) -- prettyTCM binds
          ]
{- WE CANNOT USE THIS BINDING
       -- We add a first let-binding for the value of e.
       x <- freshNoName (getRange e)
       addLetBinding Relevant x v t $ do
 -}
        -- We create a substitution for the let-bound variables
        -- (unfortunately, we cannot refer to x in internal syntax
        -- so we have to copy v).
        let sigma = zipWith ($) fs (repeat v)
        -- We apply the types of the let bound-variables to this substitution.
        -- The 0th variable in a context is the last one, so we reverse.
        -- Further, we need to lower all other de Bruijn indices by
        -- the size of delta, so we append the identity substitution.
        let sub    = parallelS (reverse sigma)
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

checkLetBinding (A.LetApply i x modapp rd rm) ret = do
  -- Any variables in the context that doesn't belong to the current
  -- module should go with the new module.
  -- fv   <- getDefFreeVars =<< (qnameFromList . mnameToList) <$> currentModule
  fv   <- getModuleFreeVars =<< currentModule
  n    <- getContextSize
  let new = n - fv
  reportSLn "tc.term.let.apply" 10 $ "Applying " ++ show modapp ++ " with " ++ show new ++ " free variables"
  reportSDoc "tc.term.let.apply" 20 $ vcat
    [ text "context =" <+> (prettyTCM =<< getContextTelescope)
    , text "module  =" <+> (prettyTCM =<< currentModule)
    , text "fv      =" <+> (text $ show fv)
    ]
  checkSectionApplication i x modapp rd rm
  withAnonymousModule x new ret
-- LetOpen is only used for highlighting and has no semantics
checkLetBinding A.LetOpen{} ret = ret

class ConvColor a i where
  convColor :: a -> i

instance ConvColor A.ArgInfo I.ArgInfo where
  convColor = mapArgInfoColors $ const [] -- "TODO guilhem 5"

instance ConvColor (A.Arg e) (I.Arg e) where
  convColor = mapArgInfo convColor

instance ConvColor (A.Dom e) (I.Dom e) where
  convColor = mapDomInfo convColor

instance ConvColor a i => ConvColor [a] [i] where
  convColor = map convColor
