{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Application
  ( checkArguments
  , checkArguments_
  , checkApplication
  , inferApplication
  ) where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>), null )
#else
import Prelude hiding ( null )
#endif

import Control.Arrow (first, second)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Reader

import Data.Maybe
import qualified Data.List as List
import Data.Either (partitionEithers)
import Data.Traversable (sequenceA)
import Data.Void
import qualified Data.IntSet as IntSet

import Agda.Interaction.Highlighting.Generate (storeDisambiguatedName)
import Agda.Interaction.Options

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Concrete.Pretty () -- only Pretty instances
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Internal as I
import Agda.Syntax.Position

import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Names
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rules.Def
import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.NonemptyList
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-----------------------------------------------------------------------------
-- * Applications
-----------------------------------------------------------------------------

-- | @checkApplication hd args e t@ checks an application.
--   Precondition: @Application hs args = appView e@
--
--   @checkApplication@ disambiguates constructors
--   (and continues to 'checkConstructorApplication')
--   and resolves pattern synonyms.
checkApplication :: Comparison -> A.Expr -> A.Args -> A.Expr -> Type -> TCM Term
checkApplication cmp hd args e t = do
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
    -- Subcase: unambiguous projection
    A.Proj _ p | Just _ <- getUnambiguous p -> checkHeadApplication cmp e t hd args

    -- Subcase: ambiguous projection
    A.Proj o p -> checkProjApp cmp e o (unAmbQ p) args t

    -- Subcase: unambiguous constructor
    A.Con ambC | Just c <- getUnambiguous ambC -> do
      -- augment c with record fields, but do not revert to original name
      con <- fromRightM (sigError __IMPOSSIBLE_VERBOSE__ (typeError $ AbstractConstructorNotInScope c)) $
        getOrigConHead c
      checkConstructorApplication cmp e t con args

    -- Subcase: ambiguous constructor
    A.Con (AmbQ cs0) -> disambiguateConstructor cs0 t >>= \ case
      Left unblock -> postponeTypeCheckingProblem (CheckExpr cmp e t) unblock
      Right c      -> checkConstructorApplication cmp e t c args

    -- Subcase: pattern synonym
    A.PatternSyn n -> do
      (ns, p) <- lookupPatternSyn n
      p <- return $ setRange (getRange n) $ killRange $ vacuous p   -- Pattern' Void -> Pattern' Expr
      -- Expand the pattern synonym by substituting for
      -- the arguments we have got and lambda-lifting
      -- over the ones we haven't.
      let meta r = A.Underscore $ A.emptyMetaInfo{ A.metaRange = r }   -- TODO: name suggestion
      case A.insertImplicitPatSynArgs meta (getRange n) ns args of
        Nothing      -> typeError $ BadArgumentsToPatternSynonym n
        Just (s, ns) -> do
          let p' = A.patternToExpr p
              e' = A.lambdaLiftExpr (map unArg ns) (A.substExpr s p')
          checkExpr' cmp e' t

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
              (A.App (A.defaultAppInfo (getRange a)) (A.QuoteTerm A.exprNoRange) . defaultNamedArg) a
          mkArg t a | unEl t == tName =
            (fmap . fmap)
              (A.App (A.defaultAppInfo (getRange a)) (A.Quote A.exprNoRange) . defaultNamedArg) a
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
          unq = A.App (A.defaultAppInfo $ fuseRange x args) (A.Unquote A.exprNoRange) . defaultNamedArg

          desugared = A.app (unq $ unAppView $ Application (A.Def x) $ macroArgs) otherArgs

      checkExpr' cmp desugared t

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
          target <- addContext tel newTypeMeta_      -- Z x y
          let holeType = telePi_ tel target         -- (x : X) (y : Y x) → Z x y
          (Just vs, EmptyTel) <- mapFst allApplyElims <$> checkArguments_ ExpandLast (getRange args) args tel
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
          ExtendTel dom . Abs "x" <$> addContext ("x", dom) (metaTel args)

    -- Subcase: defined symbol or variable.
    _ -> do
      v <- checkHeadApplication cmp e t hd args
      reportSDoc "tc.term.app" 30 $ vcat
        [ text "checkApplication: checkHeadApplication returned"
        , nest 2 $ text "v = " <+> prettyTCM v
        ]
      return v

-- | Precondition: @Application hd args = appView e@.
inferApplication :: ExpandHidden -> A.Expr -> A.Args -> A.Expr -> TCM (Term, Type)
inferApplication exh hd args e | not (defOrVar hd) = do
  t <- workOnTypes $ newTypeMeta_
  v <- checkExpr' CmpEq e t
  return (v, t)
inferApplication exh hd args e =
  case unScope hd of
    A.Proj o p | isAmbiguous p -> inferProjApp e o (unAmbQ p) args
    _ -> do
      (f, t0) <- inferHead hd
      let r = getRange hd
      res <- runExceptT $ checkArgumentsE exh (getRange hd) args t0 Nothing
      case res of
        Right (vs, t1, _) -> (,t1) <$> unfoldInlined (f vs)
        Left problem -> do
          t <- workOnTypes $ newTypeMeta_
          v <- postponeArgs problem exh r args t $ \ vs _ _ -> unfoldInlined (f vs)
          return (v, t)

-----------------------------------------------------------------------------
-- * Heads
-----------------------------------------------------------------------------

inferHeadDef :: ProjOrigin -> QName -> TCM (Elims -> Term, Type)
inferHeadDef o x = do
  proj <- isProjection x
  let app =
        case proj of
          Nothing -> \ args -> Def x $ map Apply args
          Just p  -> \ args -> projDropParsApply p o args
  mapFst applyE <$> inferDef app x

-- | Infer the type of a head thing (variable, function symbol, or constructor).
--   We return a function that applies the head to arguments.
--   This is because in case of a constructor we want to drop the parameters.
inferHead :: A.Expr -> TCM (Elims -> Term, Type)
inferHead e = do
  case e of
    A.Var x -> do -- traceCall (InferVar x) $ do
      (u, a) <- getVarInfo x
      reportSDoc "tc.term.var" 20 $ hsep
        [ text "variable" , prettyTCM x
        , text "(" , text (show u) , text ")"
        , text "has type:" , prettyTCM a
        ]
      when (unusableRelevance $ getRelevance a) $
        typeError $ VariableIsIrrelevant x
      return (applyE u, unDom a)

    A.Def x -> inferHeadDef ProjPrefix x

    A.Proj o ambP | Just d <- getUnambiguous ambP -> inferHeadDef o d
    A.Proj{} -> __IMPOSSIBLE__ -- inferHead will only be called on unambiguous projections

    A.Con ambC | Just c <- getUnambiguous ambC -> do

      -- Constructors are polymorphic internally.
      -- So, when building the constructor term
      -- we should throw away arguments corresponding to parameters.

      -- First, inferDef will try to apply the constructor
      -- to the free parameters of the current context. We ignore that.
      con <- fromRightM (sigError __IMPOSSIBLE_VERBOSE__ (typeError $ AbstractConstructorNotInScope c)) $
        getOrigConHead c
      (u, a) <- inferDef (\ _ -> Con con ConOCon []) c

      -- Next get the number of parameters in the current context.
      Constructor{conPars = n} <- theDef <$> (instantiateDef =<< getConstInfo c)

      reportSLn "tc.term.con" 7 $ unwords [prettyShow c, "has", show n, "parameters."]

      -- So when applying the constructor throw away the parameters.
      return (applyE u . drop n, a)
    A.Con{} -> __IMPOSSIBLE__  -- inferHead will only be called on unambiguous constructors
    A.QuestionMark i ii -> inferMeta (newQuestionMark ii) i
    A.Underscore i   -> inferMeta (newValueMeta RunMetaOccursCheck) i
    e -> do
      (term, t) <- inferExpr e
      return (applyE term, t)

inferDef :: (Args -> Term) -> QName -> TCM (Term, Type)
inferDef mkTerm x =
  traceCall (InferDef x) $ do
    -- getConstInfo retrieves the *absolute* (closed) type of x
    -- instantiateDef relativizes it to the current context
    d  <- instantiateDef =<< getConstInfo x
    -- irrelevant defs are only allowed in irrelevant position
    checkRelevance x d
    case theDef d of
      GeneralizableVar{} -> do
        -- Generalizable variables corresponds to metas created
        -- at the point where they should be generalized. Module parameters
        -- have already been applied to the meta, so we don't have to do that
        -- here.
        val <- fromMaybe __IMPOSSIBLE__ <$> view (eGeneralizedVars . key x)
        sub <- checkpointSubstitution (genvalCheckpoint val)
        let (v, t) = applySubst sub (genvalTerm val, genvalType val)
        debug [] t v
        return (v, t)
      _ -> do
        -- since x is considered living in the top-level, we have to
        -- apply it to the current context
        vs <- freeVarsToApply x
        let t = defType d
            v = mkTerm vs -- applies x to vs, dropping parameters
        debug vs t v
        return (v, t)
  where
    debug :: Args -> Type -> Term -> TCM ()
    debug vs t v = do
      reportSDoc "tc.term.def" 60 $
        text "freeVarsToApply to def " <+> hsep (map (text . show) vs)
      reportSDoc "tc.term.def" 10 $ vcat
        [ text "inferred def " <+> prettyTCM x <+> hsep (map prettyTCM vs)
        , nest 2 $ text ":" <+> prettyTCM t
        , nest 2 $ text "-->" <+> prettyTCM v ]

-- | The second argument is the definition of the first.
checkRelevance :: QName -> Definition -> TCM ()
checkRelevance x def = maybe (return ()) typeError =<< checkRelevance' x def

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkRelevance' :: QName -> Definition -> TCM (Maybe TypeError)
checkRelevance' x def = do
  case defRelevance def of
    Relevant -> return Nothing -- relevance functions can be used in any context.
    drel -> do
      -- Andreas,, 2018-06-09, issue #2170
      -- irrelevant projections are only allowed if --irrelevant-projections
      ifM (return (isJust $ isProjection_ $ theDef def) `and2M`
           (not .optIrrelevantProjections <$> pragmaOptions)) {-then-} needIrrProj {-else-} $ do
        rel <- asks envRelevance
        reportSDoc "tc.irr" 50 $ vcat
          [ text "declaration relevance =" <+> text (show drel)
          , text "context     relevance =" <+> text (show rel)
          ]
        return $ if (drel `moreRelevant` rel) then Nothing else Just $ DefinitionIsIrrelevant x
  where
  needIrrProj = Just . GenericDocError <$> do
    sep [ text "Projection " , prettyTCM x, text " is irrelevant."
        , text " Turn on option --irrelevant-projections to use it (unsafe)."
        ]


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
checkHeadApplication :: Comparison -> A.Expr -> Type -> A.Expr -> [NamedArg A.Expr] -> TCM Term
checkHeadApplication cmp e t hd args = do
  sharp <- fmap nameOfSharp <$> coinductionKit
  conId <- fmap getPrimName <$> getBuiltin' builtinConId
  pOr   <- fmap primFunName <$> getPrimitive' "primPOr"
  pComp <- fmap primFunName <$> getPrimitive' "primComp"
  pHComp <- fmap primFunName <$> getPrimitive' builtinHComp
  pTrans <- fmap primFunName <$> getPrimitive' builtinTrans
  mglue <- getPrimitiveName' builtin_glue
  case hd of
    -- Type checking #. The # that the user can write will be a Def, but the
    -- sharp we generate in the body of the wrapper is a Con.
    A.Def c | Just c == sharp -> checkSharpApplication e t c args

    -- Cubical primitives
    A.Def c | Just c == pComp -> defaultResult' $ Just $ checkPrimComp c
    A.Def c | Just c == pHComp -> defaultResult' $ Just $ checkPrimHComp c
    A.Def c | Just c == pTrans -> defaultResult' $ Just $ checkPrimTrans c
    A.Def c | Just c == conId -> defaultResult' $ Just $ checkConId c
    A.Def c | Just c == pOr   -> defaultResult' $ Just $ checkPOr c
    A.Def c | Just c == mglue -> defaultResult' $ Just $ checkGlue c

    _ -> defaultResult
  where
  defaultResult = defaultResult' Nothing
  defaultResult' mk = do
    (f, t0) <- inferHead hd
    expandLast <- asks envExpandLast
    checkArguments expandLast (getRange hd) args t0 t $ \ vs t1 checkedTarget -> do
      let check = do
           k <- mk
           as <- allApplyElims vs
           pure $ k as t1
      v <- unfoldInlined (f vs)
      maybe id (\ ck m -> blockTerm t $ ck >> m) check $ coerce' cmp checkedTarget v t1 t

-----------------------------------------------------------------------------
-- * Spines
-----------------------------------------------------------------------------

traceCallE :: Call -> ExceptT e TCM r -> ExceptT e TCM r
traceCallE call m = do
  z <- lift $ traceCall call $ runExceptT m
  case z of
    Right e  -> return e
    Left err -> throwError err

-- | If we've already checked the target type we don't have to call coerce.
coerce' :: Comparison -> CheckedTarget -> Term -> Type -> Type -> TCM Term
coerce' cmp NotCheckedTarget           v inferred expected = coerce cmp v inferred expected
coerce' cmp (CheckedTarget Nothing)    v _        _        = return v
coerce' cmp (CheckedTarget (Just pid)) v _        expected = blockTermOnProblem expected v pid

-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t0'@ and @args : Delta@. Inserts hidden arguments to
--   make this happen.  Returns the evaluated arguments @vs@, the remaining
--   type @t0'@ (which should be a subtype of @t1@) and any constraints @cs@
--   that have to be solved for everything to be well-formed.

checkArgumentsE :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Maybe Type ->
                   ExceptT (Elims, [NamedArg A.Expr], Type) TCM (Elims, Type, CheckedTarget)
checkArgumentsE = checkArgumentsE' NotCheckedTarget

checkArgumentsE' :: CheckedTarget -> ExpandHidden -> Range -> [NamedArg A.Expr] -> Type ->
                    Maybe Type -> ExceptT (Elims, [NamedArg A.Expr], Type) TCM (Elims, Type, CheckedTarget)
-- Case: no arguments, do not insert trailing hidden arguments: We are done.
checkArgumentsE' chk DontExpandLast _ [] t0 _ = return ([], t0, chk)

-- Case: no arguments, but need to insert trailing hiddens.
checkArgumentsE' chk ExpandLast r [] t0 mt1 =
    traceCallE (CheckArguments r [] t0 mt1) $ lift $ do
      mt1' <- traverse (unEl <.> reduce) mt1
      (us, t) <- implicitArgs (-1) (expand mt1') t0
      return (map Apply us, t, chk)
    where
      expand (Just (Pi dom _)) Hidden     = not (hidden dom)
      expand _                 Hidden     = True
      expand (Just (Pi dom _)) Instance{} = not (isInstance dom)
      expand _                 Instance{} = True
      expand _                 NotHidden  = False

-- Case: argument given.
checkArgumentsE' chk exh r args0@(arg@(Arg info e) : args) t0 mt1 =
    traceCallE (CheckArguments r args0 t0 mt1) $ do
      lift $ reportSDoc "tc.term.args" 30 $ sep
        [ text "checkArgumentsE"
--        , text "  args0 =" <+> prettyA args0
        , nest 2 $ vcat
          [ text "e     =" <+> prettyA e
          , text "t0    =" <+> prettyTCM t0
          , text "t1    =" <+> maybe (text "Nothing") prettyTCM mt1
          ]
        ]
      -- First, insert implicit arguments, depending on current argument @arg@.
      let hx = getHiding info  -- hiding of current argument
          mx = fmap rangedThing $ nameOf e -- name of current argument
          -- do not insert visible arguments
          expand NotHidden y = False
          -- insert a hidden argument if arg is not hidden or has different name
          -- insert an instance argument if arg is not instance  or has different name
          expand hy        y = not (sameHiding hy hx) || maybe False (y /=) mx
      (nargs, t) <- lift $ implicitNamedArgs (-1) expand t0
      -- Separate names from args.
      let (mxs, us) = unzip $ map (\ (Arg ai (Named mx u)) -> (mx, Apply $ Arg ai u)) nargs
          xs        = catMaybes mxs

      -- We need a function type here, but we don't know which kind
      -- (implicit/explicit). But it might be possible to use injectivity to
      -- force a pi.
      t <- lift $ forcePiUsingInjectivity t

      -- We are done inserting implicit args.  Now, try to check @arg@.
      ifBlockedType t (\ m t -> throwError (us, args0, t)) $ \ _ t0' -> do

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

        viewPath <- lift pathView'

        -- Check the target type if we can get away with it.
        chk' <- lift $
          case (chk, mt1) of
            (NotCheckedTarget, Just t1) | all visible args0 -> do
              let n = length args0
              TelV tel tgt <- telViewUpTo n t0'
              let dep = any (< n) $ IntSet.toList $ freeVars tgt
                  vis = all visible (telToList tel)
                  isRigid t | PathType{} <- viewPath t = return False -- Path is not rigid!
                  isRigid (El _ (Pi dom _)) = return $ visible dom
                  isRigid (El _ (Def d _))  = theDef <$> getConstInfo d >>= return . \ case
                    Axiom{}                   -> True
                    AbstractDefn{}            -> True
                    Function{funClauses = cs} -> null cs
                    Datatype{}                -> True
                    Record{}                  -> True
                    Constructor{}             -> __IMPOSSIBLE__
                    GeneralizableVar{}        -> __IMPOSSIBLE__
                    Primitive{}               -> False
                  isRigid _           = return False
              rigid <- isRigid tgt
              if | dep       -> return chk    -- must be non-dependent
                 | not rigid -> return chk    -- with a rigid target
                 | not vis   -> return chk    -- and only visible arguments
                 | otherwise -> do
                  let tgt1 = applySubst (strengthenS __IMPOSSIBLE__ $ size tel) tgt
                  reportSDoc "tc.term.args.target" 30 $ vcat
                    [ text "Checking target types first"
                    , nest 2 $ text "inferred =" <+> prettyTCM tgt1
                    , nest 2 $ text "expected =" <+> prettyTCM t1 ]
                  traceCall (CheckTargetType (fuseRange r args0) tgt1 t1) $
                    CheckedTarget <$> ifNoConstraints_ (leqType tgt1 t1)
                                        (return Nothing) (return . Just)

            _ -> return chk

        -- t0' <- lift $ forcePi (getHiding info) (maybe "_" rangedThing $ nameOf e) t0'
        case unEl t0' of
          Pi (Dom{domInfo = info', unDom = a}) b
            | sameHiding info info'
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
                addCheckedArgs us (Apply $ Arg info' u) $
                  checkArgumentsE' chk' exh (fuseRange r e) args (absApp b u) mt1
            | otherwise -> do
                reportSDoc "error" 10 $ nest 2 $ vcat
                  [ text $ "info      = " ++ show info
                  , text $ "info'     = " ++ show info'
                  , text $ "absName b = " ++ absName b
                  , text $ "nameOf e  = " ++ show (nameOf e)
                  ]
                wrongPi
          _
            | visible info
            , PathType s _ _ bA x y <- viewPath t0' -> do
                lift $ reportSDoc "tc.term.args" 30 $ text $ show bA
                u <- lift $ checkExpr (namedThing e) =<< elInf primInterval
                addCheckedArgs us (IApply (unArg x) (unArg y) u) $
                  checkArgumentsE exh (fuseRange r e) args (El s $ unArg bA `apply` [argN u]) mt1
          _ -> shouldBePi
  where
    addCheckedArgs us u rec = do
        (vs, t, chk) <- rec
        return (us ++ u : vs, t, chk)
      `catchError` \ (vs, es, t) ->
          throwError (us ++ u : vs, es, t)

-- | Check that a list of arguments fits a telescope.
--   Inserts hidden arguments as necessary.
--   Returns the type-checked arguments and the remaining telescope.
checkArguments_
  :: ExpandHidden         -- ^ Eagerly insert trailing hidden arguments?
  -> Range                -- ^ Range of application.
  -> [NamedArg A.Expr]    -- ^ Arguments to check.
  -> Telescope            -- ^ Telescope to check arguments against.
  -> TCM (Elims, Telescope)
     -- ^ Checked arguments and remaining telescope if successful.
checkArguments_ exh r args tel = do
    z <- runExceptT $
      checkArgumentsE exh r args (telePi tel __DUMMY_TYPE__) Nothing
    case z of
      Right (args, t, _) -> do
        let TelV tel' _ = telView' t
        return (args, tel')
      Left _ -> __IMPOSSIBLE__  -- type cannot be blocked as it is generated by telePi

-- | @checkArguments exph r args t0 t k@ tries @checkArgumentsE exph args t0 t@.
-- If it succeeds, it continues @k@ with the returned results.  If it fails,
-- it registers a postponed typechecking problem and returns the resulting new
-- meta variable.
--
-- Checks @e := ((_ : t0) args) : t@.
checkArguments ::
  ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
  (Elims -> Type -> CheckedTarget -> TCM Term) -> TCM Term
checkArguments exph r args t0 t k = do
  z <- runExceptT $ checkArgumentsE exph r args t0 (Just t)
  case z of
    Right (vs, t1, pid) -> k vs t1 pid
      -- vs = evaluated args
      -- t1 = remaining type (needs to be subtype of t)
    Left problem -> postponeArgs problem exph r args t k
      -- if unsuccessful, postpone checking until t0 unblocks

postponeArgs :: (Elims, [NamedArg A.Expr], Type) -> ExpandHidden -> Range -> [NamedArg A.Expr] -> Type ->
                (Elims -> Type -> CheckedTarget -> TCM Term) -> TCM Term
postponeArgs (us, es, t0) exph r args t k = do
  reportSDoc "tc.term.expr.args" 80 $
    sep [ text "postponed checking arguments"
        , nest 4 $ prettyList (map (prettyA . namedThing . unArg) args)
        , nest 2 $ text "against"
        , nest 4 $ prettyTCM t0 ] $$
    sep [ text "progress:"
        , nest 2 $ text "checked" <+> prettyList (map prettyTCM us)
        , nest 2 $ text "remaining" <+> sep [ prettyList (map (prettyA . namedThing . unArg) es)
                                            , nest 2 $ text ":" <+> prettyTCM t0 ] ]
  postponeTypeCheckingProblem_ (CheckArgs exph r es t0 t $ \ vs t pid -> k (us ++ vs) t pid)

-----------------------------------------------------------------------------
-- * Constructors
-----------------------------------------------------------------------------

-- | Check the type of a constructor application. This is easier than
--   a general application since the implicit arguments can be inserted
--   without looking at the arguments to the constructor.
checkConstructorApplication :: Comparison -> A.Expr -> Type -> ConHead -> [NamedArg A.Expr] -> TCM Term
checkConstructorApplication cmp org t c args = do
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
    case (t0, unEl t) of -- Only fully applied constructors get special treatment
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
           let ps    = take n $ drop (n' - n) vs
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
           checkArguments expandLast (getRange c) args' ctype' t $ \ es t' targetCheck -> do
             reportSDoc "tc.term.con" 20 $ nest 2 $ vcat
               [ text "es     =" <+> prettyTCM es
               , text "t'     =" <+> prettyTCM t' ]
             coerce' cmp targetCheck (Con c ConOCon es) t' t
      _ -> do
        reportSDoc "tc.term.con" 50 $ nest 2 $ text "we are not at a datatype, falling back"
        fallback
  where
    fallback = checkHeadApplication cmp org t (A.Con (unambiguous $ conName c)) args

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
        unnamedPar h = dropPar (sameHiding h)

        dropPar this (p : ps) | this p    = Just ps
                              | otherwise = dropPar this ps
        dropPar _ [] = Nothing

-- | Returns an unblocking action in case of failure.
disambiguateConstructor :: NonemptyList QName -> Type -> TCM (Either (TCM Bool) ConHead)
disambiguateConstructor cs0 t = do
  reportSLn "tc.check.term" 40 $ "Ambiguous constructor: " ++ prettyShow cs0

  -- Get the datatypes of the various constructors
  let getData Constructor{conData = d} = d
      getData _                        = __IMPOSSIBLE__
  reportSLn "tc.check.term" 40 $ "  ranges before: " ++ show (getRange cs0)
  -- We use the reduced constructor when disambiguating, but
  -- the original constructor for type checking. This is important
  -- since they may have different types (different parameters).
  -- See issue 279.
  -- Andreas, 2017-08-13, issue #2686: ignore abstract constructors
  (cs, cons)  <- unzip . snd . partitionEithers <$> do
     forM (toList cs0) $ \ c -> mapRight (c,) <$> getConForm c
  reportSLn "tc.check.term" 40 $ "  reduced: " ++ prettyShow cons
  case cons of
    []    -> typeError $ AbstractConstructorNotInScope $ headNe cs0
    [con] -> do
      let c = setConName (fromMaybe __IMPOSSIBLE__ $ headMaybe cs) con
      reportSLn "tc.check.term" 40 $ "  only one non-abstract constructor: " ++ prettyShow c
      storeDisambiguatedName $ conName c
      return (Right c)
    _   -> do
      dcs <- zipWithM (\ c con -> (, setConName c con) . getData . theDef <$> getConInfo con) cs cons
      -- Type error
      let badCon t = typeError $ flip DoesNotConstructAnElementOf t $
            fromMaybe __IMPOSSIBLE__ $ headMaybe cs
      -- Lets look at the target type at this point
      let getCon :: TCM (Maybe ConHead)
          getCon = do
            TelV tel t1 <- telView t
            addContext tel $ do
             reportSDoc "tc.check.term.con" 40 $ nest 2 $
               text "target type: " <+> prettyTCM t1
             ifBlockedType t1 (\ m t -> return Nothing) $ \ _ t' ->
               caseMaybeM (isDataOrRecord $ unEl t') (badCon t') $ \ d ->
                 case [ c | (d', c) <- dcs, d == d' ] of
                   [c] -> do
                     reportSLn "tc.check.term" 40 $ "  decided on: " ++ prettyShow c
                     storeDisambiguatedName $ conName c
                     return $ Just c
                   []  -> badCon $ t' $> Def d []
                   cs  -> typeError $ CantResolveOverloadedConstructorsTargetingSameDatatype d $ map conName cs
      getCon >>= \ case
        Nothing -> return $ Left $ isJust <$> getCon
        Just c  -> return $ Right c

---------------------------------------------------------------------------
-- * Projections
---------------------------------------------------------------------------

-- | Inferring the type of an overloaded projection application.
--   See 'inferOrCheckProjApp'.

inferProjApp :: A.Expr -> ProjOrigin -> NonemptyList QName -> A.Args -> TCM (Term, Type)
inferProjApp e o ds args0 = do
  (v, t, _) <- inferOrCheckProjApp e o ds args0 Nothing
  return (v, t)

-- | Checking the type of an overloaded projection application.
--   See 'inferOrCheckProjApp'.

checkProjApp  :: Comparison -> A.Expr -> ProjOrigin -> NonemptyList QName -> A.Args -> Type -> TCM Term
checkProjApp cmp e o ds args0 t = do
  (v, ti, targetCheck) <- inferOrCheckProjApp e o ds args0 (Just (cmp, t))
  coerce' cmp targetCheck v ti t

-- | Inferring or Checking an overloaded projection application.
--
--   The overloaded projection is disambiguated by inferring the type of its
--   principal argument, which is the first visible argument.

inferOrCheckProjApp
  :: A.Expr
     -- ^ The whole expression which constitutes the application.
  -> ProjOrigin
     -- ^ The origin of the projection involved in this projection application.
  -> NonemptyList QName
     -- ^ The projection name (potentially ambiguous).
  -> A.Args
     -- ^ The arguments to the projection.
  -> Maybe (Comparison, Type)
     -- ^ The expected type of the expression (if 'Nothing', infer it).
  -> TCM (Term, Type, CheckedTarget)
     -- ^ The type-checked expression and its type (if successful).
inferOrCheckProjApp e o ds args mt = do
  reportSDoc "tc.proj.amb" 20 $ vcat
    [ text "checking ambiguous projection"
    , text $ "  ds   = " ++ prettyShow ds
    , text   "  args = " <+> sep (map prettyTCM args)
    , text   "  t    = " <+> caseMaybe mt (text "Nothing") prettyTCM
    ]

  let refuse :: String -> TCM a
      refuse reason = typeError $ GenericError $
        "Cannot resolve overloaded projection "
        ++ prettyShow (A.nameConcrete $ A.qnameName $ headNe ds)
        ++ " because " ++ reason
      refuseNotApplied = refuse "it is not applied to a visible argument"
      refuseNoMatching = refuse "no matching candidate found"
      refuseNotRecordType = refuse "principal argument is not of record type"

      cmp = caseMaybe mt CmpEq fst

      -- Postpone the whole type checking problem
      -- if type of principal argument (or the type where we get it from)
      -- is blocked by meta m.
      postpone m = do
        tc <- caseMaybe mt newTypeMeta_ (return . snd)
        v <- postponeTypeCheckingProblem (CheckExpr cmp e tc) $ isInstantiatedMeta m
        return (v, tc, NotCheckedTarget)

  -- The following cases need to be considered:
  -- 1. No arguments to the projection.
  -- 2. Arguments (parameters), but not the principal argument.
  -- 3. Argument(s) including the principal argument.

  -- For now, we only allow ambiguous projections if the first visible
  -- argument is the record value.

  case filter (visible . snd) $ zip [0..] args of

    -- Case: we have no visible argument to the projection.
    -- In inference mode, we really need the visible argument, postponing does not help
    [] -> caseMaybe mt refuseNotApplied $ \ (cmp , t) -> do
      -- If we have the type, we can try to get the type of the principal argument.
      -- It is the first visible argument.
      TelV _ptel core <- telViewUpTo' (-1) (not . visible) t
      ifBlockedType core (\ m _ -> postpone m) $ {-else-} \ _ core -> do
      ifNotPiType core (\ _ -> refuseNotApplied) $ {-else-} \ dom _b -> do
      ifBlockedType (unDom dom) (\ m _ -> postpone m) $ {-else-} \ _ ta -> do
      caseMaybeM (isRecordType ta) refuseNotRecordType $ \ (_q, _pars, defn) -> do
      case defn of
        Record { recFields = fs } -> do
          case catMaybes $ for fs $ \ (Arg _ f) -> List.find (f ==) (toList ds) of
            [] -> refuseNoMatching
            [d] -> do
              storeDisambiguatedName d
              -- checkHeadApplication will check the target type
              (, t, CheckedTarget Nothing) <$>
                checkHeadApplication cmp e t (A.Proj o $ unambiguous d) args
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
      ifBlockedType ta (\ m _ -> postpone m) {-else-} $ \ _ ta -> do
      caseMaybeM (isRecordType ta) refuseNotRecordType $ \ (q, _pars0, _) -> do

          -- try to project it with all of the possible projections
          let try d = do
                reportSDoc "tc.proj.amb" 30 $ vcat
                  [ text $ "trying projection " ++ prettyShow d
                  , text "  td  = " <+> caseMaybeM (getDefType d ta) (text "Nothing") prettyTCM
                  ]

                -- get the original projection name
                def <- lift $ getConstInfo d
                let isP = isProjection_ $ theDef def
                reportSDoc "tc.proj.amb" 40 $ vcat $
                  [ text $ "  isProjection = " ++ caseMaybe isP "no" (const "yes")
                  ] ++ caseMaybe isP [] (\ Projection{ projProper = proper, projOrig = orig } ->
                  [ text $ "  proper       = " ++ show proper
                  , text $ "  orig         = " ++ prettyShow orig
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
                let tfull = defType def
                TelV tel _ <- lift $ telViewUpTo' (-1) (not . visible) tfull
                reportSDoc "tc.proj.amb" 30 $ vcat
                  [ text $ "  size tel  = " ++ show (size tel)
                  , text $ "  size pars = " ++ show (size pars)
                  ]
                -- See issue 1960 for when the following assertion fails for
                -- the correct disambiguation.
                -- guard (size tel == size pars)

                guard =<< do isNothing <$> do lift $ checkRelevance' d def
                return (orig, (d, (pars, (dom, u, tb))))

          cands <- groupOn fst . catMaybes <$> mapM (runMaybeT . try) (toList ds)
          case cands of
            [] -> refuseNoMatching
            [[]] -> refuseNoMatching
            (_:_:_) -> refuse $ "several matching candidates found: "
                 ++ prettyShow (map (fst . snd) $ concat cands)
            -- case: just one matching projection d
            -- the term u = d v
            -- the type tb is the type of this application
            [ (_orig, (d, (pars, (_dom,u,tb)))) : _ ] -> do
              storeDisambiguatedName d

              -- Check parameters
              tfull <- typeOfConst d
              (_,_) <- checkKnownArguments (take k args) pars tfull

              -- Check remaining arguments
              let r     = getRange e
                  args' = drop (k + 1) args
              z <- runExceptT $ checkArgumentsE ExpandLast r args' tb (snd <$> mt)
              case z of
                Right (us, trest, targetCheck) -> return (u `applyE` us, trest, targetCheck)
                Left problem -> do
                  -- In the inference case:
                  -- To create a postponed type checking problem,
                  -- we do not use typeDontCare, but create a meta.
                  tc <- caseMaybe mt newTypeMeta_ (return . snd)
                  v  <- postponeArgs problem ExpandLast r args' tc $ \ us trest targetCheck ->
                          coerce' cmp targetCheck (u `applyE` us) trest tc

                  return (v, tc, NotCheckedTarget)

-----------------------------------------------------------------------------
-- * Coinduction
-----------------------------------------------------------------------------

checkSharpApplication :: A.Expr -> Type -> QName -> [NamedArg A.Expr] -> TCM Term
checkSharpApplication e t c args = do
  arg <- case args of
           [a] | visible a -> return $ namedArg a
           _ -> typeError $ GenericError $ prettyShow c ++ " must be applied to exactly one argument."

  -- The name of the fresh function.
  i <- fresh :: TCM Int
  let name = filter (/= '_') (prettyShow $ A.nameConcrete $ A.qnameName c) ++ "-" ++ show i

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
        core   = A.LHSProj { A.lhsDestructor = unambiguous flat
                           , A.lhsFocus      = defaultNamedArg $ A.LHSHead c' []
                           , A.lhsPats       = [] }
        clause = A.Clause (A.LHS empty core) []
                          (A.RHS arg Nothing)
                          A.noWhereDecls False

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

-----------------------------------------------------------------------------
-- * Cubical
-----------------------------------------------------------------------------

-- | "pathAbs (PathView s _ l a x y) t" builds "(\ t) : pv"
--   Preconditions: PathView is PathType, and t[i0] = x, t[i1] = y
pathAbs :: PathView -> Abs Term -> TCM Term
pathAbs (OType _) t = __IMPOSSIBLE__
pathAbs (PathType s path l a x y) t = do
  return $ Lam defaultArgInfo t

checkPrimComp :: QName -> Args -> Type -> TCM ()
checkPrimComp c vs _ = do
  case vs of
    [l, a, phi, u, a0] -> do
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      ty <- elInf $ primPartial <#> (pure $ unArg l `apply` [iz]) <@> (pure $ unArg a `apply` [iz]) <@> (pure $ unArg phi)
      equalTerm ty -- (El (getSort t1) (apply (unArg a) [iz]))
          (Lam defaultArgInfo $ NoAbs "_" $ unArg a0)
          (apply (unArg u) [iz])
    _ -> typeError $ GenericError $ show c ++ " must be fully applied"

checkPrimHComp :: QName -> Args -> Type -> TCM ()
checkPrimHComp c vs _ = do
  case vs of
    [l, a, phi, u, a0] -> do
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      ty <- elInf $ primPartial <#> (pure $ unArg l) <@> (pure $ unArg a) <@> (pure $ unArg phi)
      equalTerm ty -- (El (getSort t1) (apply (unArg a) [iz]))
          (Lam defaultArgInfo $ NoAbs "_" $ unArg a0)
          (apply (unArg u) [iz])
    _ -> typeError $ GenericError $ show c ++ " must be fully applied"

checkPrimTrans :: QName -> Args -> Type -> TCM ()
checkPrimTrans c vs _ = do
  case vs of
    [l, a, phi, a0] -> do
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      ty <- runNamesT [] $ do
        l <- open $ unArg l
        nPi' "i" (elInf $ cl primInterval) $ \ i -> (sort . tmSort <$> (l <@> i))
      equalTermOnFace (unArg phi) ty
          (unArg a)
          (Lam defaultArgInfo $ NoAbs "_" $ apply (unArg a) [iz])
    _ -> typeError $ GenericError $ show c ++ " must be fully applied"

checkConId :: QName -> Args -> Type -> TCM ()
checkConId c vs t1 = do
  case vs of
   [_, _, _, _, phi, p] -> do
      iv@(PathType s _ l a x y) <- idViewAsPath t1
      let ty = pathUnview iv
      -- the following duplicates reduction of phi
      const_x <- blockTerm ty $ do
          equalTermOnFace (unArg phi) (El s (unArg a)) (unArg x) (unArg y)
          pathAbs iv (NoAbs (stringToArgName "_") (unArg x))
      equalTermOnFace (unArg phi) ty (unArg p) const_x   -- G, phi |- p = \ i . x

      -- phi <- reduce phi
      -- forallFaceMaps (unArg phi) $ \ alpha -> do
      --   iv@(PathType s _ l a x y) <- idViewAsPath (applySubst alpha t1)
      --   let ty = pathUnview iv
      --   equalTerm (El s (unArg a)) (unArg x) (unArg y) -- precondition for cx being well-typed at ty
      --   cx <- pathAbs iv (NoAbs (stringToArgName "_") (applySubst alpha (unArg x)))
      --   equalTerm ty (applySubst alpha (unArg p)) cx   -- G, phi |- p = \ i . x
   _ -> typeError $ GenericError $ show c ++ " must be fully applied"

checkPOr :: QName -> Args -> Type -> TCM ()
checkPOr c vs t1 = do
  case vs of
   [l, phi1, phi2, a, u, v] -> do
      phi <- intervalUnview (IMin phi1 phi2)
      reportSDoc "tc.term.por" 10 $ text (show phi)
      -- phi <- reduce phi
      -- alphas <- toFaceMaps phi
      -- reportSDoc "tc.term.por" 10 $ text (show alphas)
      equalTermOnFace phi t1 (unArg u) (unArg v)
   _ -> typeError $ GenericError $ show c ++ " must be fully applied"

checkGlue :: QName -> Args -> Type -> TCM ()
checkGlue c vs _ = do
  case vs of
   [la, lb, bA, phi, bT, e, t, a] -> do
      let iinfo = setRelevance Irrelevant defaultArgInfo
      v <- runNamesT [] $ do
            [lb, la, bA, phi, bT, e, t] <- mapM (open . unArg) [lb, la, bA, phi, bT, e, t]
            let f o = cl primEquivFun <#> lb <#> la <#> (bT <..> o) <#> bA <@> (e <..> o)
            glam iinfo "o" $ \ o -> f o <@> (t <..> o)
      ty <- runNamesT [] $ do
            [lb, phi, bA] <- mapM (open . unArg) [lb, phi, bA]
            elInf $ cl primPartialP <#> lb <@> phi <@> (glam iinfo "o" $ \ _ -> bA)
      let a' = Lam iinfo (NoAbs "o" $ unArg a)
      equalTerm ty a' v
   _ -> typeError $ GenericError $ show c ++ " must be fully applied"
