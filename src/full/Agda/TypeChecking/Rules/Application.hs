{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Application
  ( checkArguments
  , checkArguments_
  , checkApplication
  , inferApplication
  , checkProjAppToKnownPrincipalArg
  ) where

import Prelude hiding ( null )

import Control.Arrow (first)
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
import Agda.TypeChecking.Free.Lazy (VarMap, lookupVarMap)
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.InstanceArguments (postponeInstanceConstraints)
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Names
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
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

import Agda.Utils.Impossible

-----------------------------------------------------------------------------
-- * Applications
-----------------------------------------------------------------------------

-- | Ranges of checked arguments, where present.
type MaybeRanges = [Maybe Range]

-- | @checkApplication hd args e t@ checks an application.
--   Precondition: @Application hs args = appView e@
--
--   @checkApplication@ disambiguates constructors
--   (and continues to 'checkConstructorApplication')
--   and resolves pattern synonyms.
checkApplication :: Comparison -> A.Expr -> A.Args -> A.Expr -> Type -> TCM Term
checkApplication cmp hd args e t = postponeInstanceConstraints $ do
  reportSDoc "tc.check.app" 20 $ vcat
    [ "checkApplication"
    , nest 2 $ "hd   = " <+> prettyA hd
    , nest 2 $ "args = " <+> sep (map prettyA args)
    , nest 2 $ "e    = " <+> prettyA e
    , nest 2 $ "t    = " <+> prettyTCM t
    ]
  reportSDoc "tc.check.app" 70 $ vcat
    [ "checkApplication (raw)"
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
            case insertImplicit arg tel of
              NoInsertNeeded -> first (mkArg (snd $ unDom d) arg :) $ makeArgs (tail tel) args
              ImpInsert is   -> makeArgs (drop (length is) tel) (arg : args)
              BadImplicits   -> (arg : args, [])  -- fail later in checkHeadApplication
              NoSuchName{}   -> (arg : args, [])  -- ditto

          (macroArgs, otherArgs) = makeArgs argTel args
          unq = A.App (A.defaultAppInfo $ fuseRange x args) (A.Unquote A.exprNoRange) . defaultNamedArg

          desugared = A.app (unq $ unAppView $ Application (A.Def x) $ macroArgs) otherArgs

      checkExpr' cmp desugared t

    -- Subcase: unquote
    A.Unquote _
      | [arg] <- args -> do
          (_, hole) <- newValueMeta RunMetaOccursCheck t
          unquoteM (namedArg arg) hole t
          return hole
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
          unquoteM (namedArg arg) hole holeType
          return $ apply hole vs
      where
        metaTel :: [Arg a] -> TCM Telescope
        metaTel []           = pure EmptyTel
        metaTel (arg : args) = do
          a <- newTypeMeta_
          let dom = a <$ domFromArg arg
          ExtendTel dom . Abs "x" <$>
            addContext ("x" :: String, dom) (metaTel args)

    -- Subcase: defined symbol or variable.
    _ -> do
      v <- checkHeadApplication cmp e t hd args
      reportSDoc "tc.term.app" 30 $ vcat
        [ "checkApplication: checkHeadApplication returned"
        , nest 2 $ "v = " <+> prettyTCM v
        ]
      return v

-- | Precondition: @Application hd args = appView e@.
inferApplication :: ExpandHidden -> A.Expr -> A.Args -> A.Expr -> TCM (Term, Type)
inferApplication exh hd args e | not (inferrableHead hd) = do
  t <- workOnTypes $ newTypeMeta_
  v <- checkExpr' CmpEq e t
  return (v, t)
inferApplication exh hd args e = postponeInstanceConstraints $
  case unScope hd of
    A.Proj o p | isAmbiguous p -> inferProjApp e o (unAmbQ p) args
    _ -> do
      (f, t0) <- inferHead hd
      let r = getRange hd
      res <- runExceptT $ checkArgumentsE exh (getRange hd) args t0 Nothing
      case res of
        Right (_, vs, t1, _) -> (,t1) <$> unfoldInlined (f vs)
        Left problem -> do
          t <- workOnTypes $ newTypeMeta_
          v <- postponeArgs problem exh r args t $ \ _ vs _ _ -> unfoldInlined (f vs)
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
        [ "variable" , prettyTCM x
        , "(" , text (show u) , ")"
        , "has type:" , prettyTCM a
        ]
      unless (usableRelevance a) $
        typeError $ VariableIsIrrelevant x
      -- Andreas, 2019-06-18, LAIM 2019, issue #3855:
      -- Conor McBride style quantity judgement:
      -- The available quantity for variable x must be below
      -- the required quantity to construct the term x.
      -- Note: this whole thing does not work for linearity, where we need some actual arithmetics.
      unlessM ((getQuantity a `moreQuantity`) <$> asksTC getQuantity) $
        typeError $ VariableIsErased x

      unless (usableCohesion a) $
        typeError $ VariableIsOfUnusableCohesion x (getCohesion a)

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
    -- Irrelevant defs are only allowed in irrelevant position.
    -- Erased defs are only allowed in erased position (see #3855).
    checkModality x d
    case theDef d of
      GeneralizableVar{} -> do
        -- Generalizable variables corresponds to metas created
        -- at the point where they should be generalized. Module parameters
        -- have already been applied to the meta, so we don't have to do that
        -- here.
        val <- fromMaybe __IMPOSSIBLE__ <$> viewTC (eGeneralizedVars . key x)
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

        -- Andrea 2019-07-16, Check that the supplied arguments
        -- respect the cohesion modalities of the current context.
        -- Cohesion is purely based on left-division, so it does not
        -- rely on "position" like Relevance/Quantity.
        checkCohesionArgs vs

        debug vs t v
        return (v, t)
  where
    debug :: Args -> Type -> Term -> TCM ()
    debug vs t v = do
      reportSDoc "tc.term.def" 60 $
        "freeVarsToApply to def " <+> hsep (map (text . show) vs)
      reportSDoc "tc.term.def" 10 $ vcat
        [ "inferred def " <+> prettyTCM x <+> hsep (map prettyTCM vs)
        , nest 2 $ ":" <+> prettyTCM t
        , nest 2 $ "-->" <+> prettyTCM v ]

checkCohesionArgs :: Args -> TCM ()
checkCohesionArgs vs = do
  let
    vmap :: VarMap
    vmap = freeVars vs

  -- we iterate over all vars in the context and their ArgInfo,
  -- checking for each that "vs" uses them as allowed.
  as <- getContextArgs
  forM_ as $ \ (Arg avail t) -> do
    let m = do
          v <- deBruijnView t
          varModality <$> lookupVarMap v vmap
    whenJust m $ \ used -> do
        unless (getCohesion avail `moreCohesion` getCohesion used) $
           (genericDocError =<<) $ fsep $
                ["Variable" , prettyTCM t]
             ++ pwords "is used as" ++ [text $ show $ getCohesion used]
             ++ pwords "but only available as" ++ [text $ show $ getCohesion avail]

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkRelevance' :: QName -> Definition -> TCM (Maybe TypeError)
checkRelevance' x def = do
  case getRelevance def of
    Relevant -> return Nothing -- relevance functions can be used in any context.
    drel -> do
      -- Andreas,, 2018-06-09, issue #2170
      -- irrelevant projections are only allowed if --irrelevant-projections
      ifM (return (isJust $ isProjection_ $ theDef def) `and2M`
           (not .optIrrelevantProjections <$> pragmaOptions)) {-then-} needIrrProj {-else-} $ do
        rel <- asksTC getRelevance
        reportSDoc "tc.irr" 50 $ vcat
          [ "declaration relevance =" <+> text (show drel)
          , "context     relevance =" <+> text (show rel)
          ]
        return $ if (drel `moreRelevant` rel) then Nothing else Just $ DefinitionIsIrrelevant x
  where
  needIrrProj = Just . GenericDocError <$> do
    sep [ "Projection " , prettyTCM x, " is irrelevant."
        , " Turn on option --irrelevant-projections to use it (unsafe)."
        ]

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkQuantity' :: QName -> Definition -> TCM (Maybe TypeError)
checkQuantity' x def = do
  case getQuantity def of
    Quantityω{} -> return Nothing -- Abundant definitions can be used in any context.
    dq -> do
      q <- asksTC getQuantity
      reportSDoc "tc.irr" 50 $ vcat
        [ "declaration quantity =" <+> text (show dq)
        , "context     quantity =" <+> text (show q)
        ]
      return $ if (dq `moreQuantity` q) then Nothing else Just $ DefinitionIsErased x

-- | The second argument is the definition of the first.
checkModality' :: QName -> Definition -> TCM (Maybe TypeError)
checkModality' x def = do
  checkRelevance' x def >>= \case
    Nothing    -> checkQuantity' x def
    err@Just{} -> return err

-- | The second argument is the definition of the first.
checkModality :: QName -> Definition -> TCM ()
checkModality x def = justToError $ checkModality' x def
  where
  justToError m = maybe (return ()) typeError =<< m

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
  conId  <- getNameOfConstrained builtinConId
  pOr    <- getNameOfConstrained builtinPOr
  pComp  <- getNameOfConstrained builtinComp
  pHComp <- getNameOfConstrained builtinHComp
  pTrans <- getNameOfConstrained builtinTrans
  mglue  <- getNameOfConstrained builtin_glue
  mglueU  <- getNameOfConstrained builtin_glueU
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
    A.Def c | Just c == mglue -> defaultResult' $ Just $ check_glue c
    A.Def c | Just c == mglueU -> defaultResult' $ Just $ check_glueU c

    _ -> defaultResult
  where
  defaultResult :: TCM Term
  defaultResult = defaultResult' Nothing
  defaultResult' :: Maybe (MaybeRanges -> Args -> Type -> TCM Args) -> TCM Term
  defaultResult' mk = do
    (f, t0) <- inferHead hd
    expandLast <- asksTC envExpandLast
    checkArguments expandLast (getRange hd) args t0 t $ \ rs vs t1 checkedTarget -> do
      let check = do
           k <- mk
           as <- allApplyElims vs
           pure $ k rs as t1
      vs <- case check of
              Just ck -> do
                map Apply <$> ck
              Nothing -> do
                return vs
      v <- unfoldInlined (f vs)
      coerce' cmp checkedTarget v t1 t

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
                   ExceptT (MaybeRanges, Elims, [NamedArg A.Expr], Type) TCM (MaybeRanges, Elims, Type, CheckedTarget)
checkArgumentsE = checkArgumentsE' NotCheckedTarget

checkArgumentsE'
  :: CheckedTarget     -- ^ Have we already checked the target?
  -> ExpandHidden      -- ^ Insert trailing hidden arguments?
  -> Range             -- ^ Range of the function.
  -> [NamedArg A.Expr] -- ^ Arguments.
  -> Type              -- ^ Type of the function.
  -> Maybe Type        -- ^ Type of the application.
  -> ExceptT (MaybeRanges, Elims, [NamedArg A.Expr], Type) TCM (MaybeRanges, Elims, Type, CheckedTarget)

-- Case: no arguments, do not insert trailing hidden arguments: We are done.
checkArgumentsE' chk DontExpandLast _ [] t0 _ = return ([], [], t0, chk)

-- Case: no arguments, but need to insert trailing hiddens.
checkArgumentsE' chk ExpandLast r [] t0 mt1 =
    traceCallE (CheckArguments r [] t0 mt1) $ lift $ do
      mt1' <- traverse (unEl <.> reduce) mt1
      (us, t) <- implicitArgs (-1) (expand mt1') t0
      return (replicate (length us) Nothing, map Apply us, t, chk)
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
        [ "checkArgumentsE"
--        , "  args0 =" <+> prettyA args0
        , nest 2 $ vcat
          [ "e     =" <+> prettyA e
          , "t0    =" <+> prettyTCM t0
          , "t1    =" <+> maybe "Nothing" prettyTCM mt1
          ]
        ]
      -- First, insert implicit arguments, depending on current argument @arg@.
      let hx = getHiding info  -- hiding of current argument
          mx :: Maybe ArgName
          mx = bareNameOf e    -- name of current argument
          -- do not insert visible arguments
          expand NotHidden y = False
          -- insert a hidden argument if arg is not hidden or has different name
          -- insert an instance argument if arg is not instance  or has different name
          expand hy        y = not (sameHiding hy hx) || maybe False (y /=) mx
      reportSDoc "tc.term.args" 30 $ vcat
        [ "calling implicitNamedArgs"
        , nest 2 $ "t0 = " <+> prettyTCM t0
        , nest 2 $ "hx = " <+> text (show hx)
        , nest 2 $ "mx = " <+> maybe "nothing" prettyTCM mx
        ]
      (nargs, t) <- lift $ implicitNamedArgs (-1) expand t0
      -- Separate names from args.
      let (mxs, us) = unzip $ map (\ (Arg ai (Named mx u)) -> (mx, Apply $ Arg ai u)) nargs
          xs        = catMaybes mxs

      -- We need a function type here, but we don't know which kind
      -- (implicit/explicit). But it might be possible to use injectivity to
      -- force a pi.
      t <- lift $ forcePiUsingInjectivity t

      -- We are done inserting implicit args.  Now, try to check @arg@.
      ifBlocked t (\ m t -> throwError (replicate (length us) Nothing, us, args0, t)) $ \ _ t0' -> do

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
              | otherwise      = lift $ typeError $ WrongNamedArgument arg xs

        -- 2. We have a function type left, but it is the wrong one.
        --    Our argument must be implicit, case a) is impossible.
        --    (Otherwise we would have ran out of function types instead.)
        let wrongPi
              -- b) We have not inserted any implicits.
              | null xs   = lift $ typeError $ WrongHidingInApplication t0'
              -- c) We inserted implicits, but did not find his one.
              | otherwise = lift $ typeError $ WrongNamedArgument arg xs

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
                    DataOrRecSig{}            -> True
                    AbstractDefn{}            -> True
                    Function{funClauses = cs} -> null cs
                    Datatype{}                -> True
                    Record{}                  -> True
                    Constructor{}             -> __IMPOSSIBLE__
                    GeneralizableVar{}        -> __IMPOSSIBLE__
                    Primitive{}               -> False
                  isRigid _           = return False
              rigid <- isRigid tgt
              -- Andreas, 2019-03-28, issue #3248:
              -- If the target type is SIZELT, we need coerce, leqType is insufficient.
              -- For example, we have i : Size <= (Size< ↑ i), but not Size <= (Size< ↑ i).
              isSizeLt <- reduce t1 >>= isSizeType <&> \case
                Just (BoundedLt _) -> True
                _ -> False
              if | dep       -> return chk    -- must be non-dependent
                 | not rigid -> return chk    -- with a rigid target
                 | not vis   -> return chk    -- and only visible arguments
                 | isSizeLt  -> return chk    -- Issue #3248, not Size<
                 | otherwise -> do
                  let tgt1 = applySubst (strengthenS __IMPOSSIBLE__ $ size tel) tgt
                  reportSDoc "tc.term.args.target" 30 $ vcat
                    [ "Checking target types first"
                    , nest 2 $ "inferred =" <+> prettyTCM tgt1
                    , nest 2 $ "expected =" <+> prettyTCM t1 ]
                  traceCall (CheckTargetType (fuseRange r args0) tgt1 t1) $
                    CheckedTarget <$> ifNoConstraints_ (leqType tgt1 t1)
                                        (return Nothing) (return . Just)

            _ -> return chk

        -- t0' <- lift $ forcePi (getHiding info) (maybe "_" rangedThing $ nameOf e) t0'
        case unEl t0' of
          Pi (Dom{domInfo = info', domName = dname, unDom = a}) b
            | let name = bareNameWithDefault "_" dname,
              sameHiding info info'
              && (visible info || maybe True (name ==) mx) -> do
                u <- lift $ applyModalityToContext info' $ do
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
                  let e' = e { nameOf = maybe dname Just (nameOf e) }
                  checkNamedArg (Arg info' e') a
                -- save relevance info' from domain in argument
                addCheckedArgs us (getRange e) (Apply $ Arg info' u) $
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
                addCheckedArgs us (getRange e) (IApply (unArg x) (unArg y) u) $
                  checkArgumentsE exh (fuseRange r e) args (El s $ unArg bA `apply` [argN u]) mt1
          _ -> shouldBePi
  where
    addCheckedArgs us r u rec = do
        (rs, vs, t, chk) <- rec
        let rs' = replicate (length us) Nothing ++ Just r : rs
        return (rs', us ++ u : vs, t, chk)
      `catchError` \ (rs, vs, es, t) -> do
          let rs' = replicate (length us) Nothing ++ Just r : rs
          throwError (rs', us ++ u : vs, es, t)

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
checkArguments_ exh r args tel = postponeInstanceConstraints $ do
    z <- runExceptT $
      checkArgumentsE exh r args (telePi tel __DUMMY_TYPE__) Nothing
    case z of
      Right (_, args, t, _) -> do
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
  (MaybeRanges -> Elims -> Type -> CheckedTarget -> TCM Term) -> TCM Term
checkArguments exph r args t0 t k = postponeInstanceConstraints $ do
  z <- runExceptT $ checkArgumentsE exph r args t0 (Just t)
  case z of
    Right (rs, vs, t1, pid) -> k rs vs t1 pid
      -- vs = evaluated args
      -- t1 = remaining type (needs to be subtype of t)
    Left problem -> postponeArgs problem exph r args t k
      -- if unsuccessful, postpone checking until t0 unblocks

postponeArgs :: (MaybeRanges, Elims, [NamedArg A.Expr], Type) -> ExpandHidden -> Range -> [NamedArg A.Expr] -> Type ->
                (MaybeRanges -> Elims -> Type -> CheckedTarget -> TCM Term) -> TCM Term
postponeArgs (rs, us, es, t0) exph r args t k = do
  reportSDoc "tc.term.expr.args" 80 $
    sep [ "postponed checking arguments"
        , nest 4 $ prettyList (map (prettyA . namedThing . unArg) args)
        , nest 2 $ "against"
        , nest 4 $ prettyTCM t0 ] $$
    sep [ "progress:"
        , nest 2 $ "checked" <+> prettyList (map prettyTCM us)
        , nest 2 $ "remaining" <+> sep [ prettyList (map (prettyA . namedThing . unArg) es)
                                            , nest 2 $ ":" <+> prettyTCM t0 ] ]
  postponeTypeCheckingProblem_ (CheckArgs exph r es t0 t $ \ rs' vs t pid -> k (rs ++ rs') (us ++ vs) t pid)

-----------------------------------------------------------------------------
-- * Constructors
-----------------------------------------------------------------------------

-- | Check the type of a constructor application. This is easier than
--   a general application since the implicit arguments can be inserted
--   without looking at the arguments to the constructor.
checkConstructorApplication :: Comparison -> A.Expr -> Type -> ConHead -> [NamedArg A.Expr] -> TCM Term
checkConstructorApplication cmp org t c args = do
  reportSDoc "tc.term.con" 50 $ vcat
    [ "entering checkConstructorApplication"
    , nest 2 $ vcat
      [ "org  =" <+> prettyTCM org
      , "t    =" <+> prettyTCM t
      , "c    =" <+> prettyTCM c
      , "args =" <+> prettyTCM args
    ] ]
  let paramsGiven = checkForParams args
  if paramsGiven then fallback else do
    reportSDoc "tc.term.con" 50 $ "checkConstructorApplication: no parameters explicitly supplied, continuing..."
    cdef  <- getConInfo c
    let Constructor{conData = d, conPars = npars} = theDef cdef
    reportSDoc "tc.term.con" 50 $ nest 2 $ "d    =" <+> prettyTCM d
    -- Issue 661: t maybe an evaluated form of d .., so we evaluate d
    -- as well and then check wether we deal with the same datatype
    t0 <- reduce (Def d [])
    case (t0, unEl t) of -- Only fully applied constructors get special treatment
      (Def d0 _, Def d' es) -> do
        let ~(Just vs) = allApplyElims es
        reportSDoc "tc.term.con" 50 $ nest 2 $ "d0   =" <+> prettyTCM d0
        reportSDoc "tc.term.con" 50 $ nest 2 $ "d'   =" <+> prettyTCM d'
        reportSDoc "tc.term.con" 50 $ nest 2 $ "vs   =" <+> prettyTCM vs
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
             [ "special checking of constructor application of" <+> prettyTCM c
             , nest 2 $ vcat [ "ps     =" <+> prettyTCM ps
                             , "ctype  =" <+> prettyTCM ctype ] ]
           let ctype' = ctype `piApply` ps
           reportSDoc "tc.term.con" 20 $ nest 2 $ "ctype' =" <+> prettyTCM ctype'
           -- get the parameter names
           let TelV ptel _ = telView'UpTo n ctype
           let pnames = map (fmap fst) $ telToList ptel
           -- drop the parameter arguments
               args' = dropArgs pnames args
           -- check the non-parameter arguments
           expandLast <- asksTC envExpandLast
           checkArguments expandLast (getRange c) args' ctype' t $ \ rs es t' targetCheck -> do
             reportSDoc "tc.term.con" 20 $ nest 2 $ vcat
               [ text "es     =" <+> prettyTCM es
               , text "t'     =" <+> prettyTCM t' ]
             coerce' cmp targetCheck (Con c ConOCon es) t' t
      _ -> do
        reportSDoc "tc.term.con" 50 $ nest 2 $ "we are not at a datatype, falling back"
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
        name = bareNameOf arg
        h    = getHiding arg

        namedPar   x = dropPar ((x ==) . unDom)
        unnamedPar h = dropPar (sameHiding h)

        dropPar this (p : ps) | this p    = Just ps
                              | otherwise = dropPar this ps
        dropPar _ [] = Nothing

-- | Returns an unblocking action in case of failure.
disambiguateConstructor :: NonemptyList QName -> Type -> TCM (Either (TCM Bool) ConHead)
disambiguateConstructor cs0 t = do
  reportSLn "tc.check.term.con" 40 $ "Ambiguous constructor: " ++ prettyShow cs0

  -- Get the datatypes of the various constructors
  let getData Constructor{conData = d} = d
      getData _                        = __IMPOSSIBLE__
  reportSLn "tc.check.term.con" 40 $ "  ranges before: " ++ show (getRange cs0)
  -- We use the reduced constructor when disambiguating, but
  -- the original constructor for type checking. This is important
  -- since they may have different types (different parameters).
  -- See issue 279.
  -- Andreas, 2017-08-13, issue #2686: ignore abstract constructors
  (cs, cons)  <- unzip . snd . partitionEithers <$> do
     forM (toList cs0) $ \ c -> mapRight (c,) <$> getConForm c
  reportSLn "tc.check.term.con" 40 $ "  reduced: " ++ prettyShow cons
  case cons of
    []    -> typeError $ AbstractConstructorNotInScope $ headNe cs0
    [con] -> do
      let c = setConName (headWithDefault __IMPOSSIBLE__ cs) con
      reportSLn "tc.check.term.con" 40 $ "  only one non-abstract constructor: " ++ prettyShow c
      storeDisambiguatedName $ conName c
      return (Right c)
    _   -> do
      dcs <- zipWithM (\ c con -> (, setConName c con) . getData . theDef <$> getConInfo con) cs cons
      -- Type error
      let badCon t = typeError $ flip DoesNotConstructAnElementOf t $
            headWithDefault __IMPOSSIBLE__ cs
      -- Lets look at the target type at this point
      let getCon :: TCM (Maybe ConHead)
          getCon = do
            TelV tel t1 <- telView t
            addContext tel $ do
             reportSDoc "tc.check.term.con" 40 $ nest 2 $
               "target type: " <+> prettyTCM t1
             ifBlocked t1 (\ m t -> return Nothing) $ \ _ t' ->
               caseMaybeM (isDataOrRecord $ unEl t') (badCon t') $ \ d ->
                 case [ c | (d', c) <- dcs, d == d' ] of
                   [c] -> do
                     reportSLn "tc.check.term.con" 40 $ "  decided on: " ++ prettyShow c
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

-- | Checking the type of an overloaded projection application.
--   See 'inferOrCheckProjAppToKnownPrincipalArg'.

checkProjAppToKnownPrincipalArg  :: Comparison -> A.Expr -> ProjOrigin -> NonemptyList QName -> A.Args -> Type -> Int -> Term -> Type -> TCM Term
checkProjAppToKnownPrincipalArg cmp e o ds args0 t k v0 pt = do
  (v, ti, targetCheck) <- inferOrCheckProjAppToKnownPrincipalArg e o ds args0 (Just (cmp, t)) k v0 pt
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
    [ "checking ambiguous projection"
    , text $ "  ds   = " ++ prettyShow ds
    , text   "  args = " <+> sep (map prettyTCM args)
    , text   "  t    = " <+> caseMaybe mt "Nothing" prettyTCM
    ]

  let cmp = caseMaybe mt CmpEq fst

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
    [] -> caseMaybe mt (refuseProjNotApplied ds) $ \ (cmp , t) -> do
      -- If we have the type, we can try to get the type of the principal argument.
      -- It is the first visible argument.
      TelV _ptel core <- telViewUpTo' (-1) (not . visible) t
      ifBlocked core (\ m _ -> postpone m) $ {-else-} \ _ core -> do
      ifNotPiType core (\ _ -> refuseProjNotApplied ds) $ {-else-} \ dom _b -> do
      ifBlocked (unDom dom) (\ m _ -> postpone m) $ {-else-} \ _ ta -> do
      caseMaybeM (isRecordType ta) (refuseProjNotRecordType ds) $ \ (_q, _pars, defn) -> do
      case defn of
        Record { recFields = fs } -> do
          case forMaybe fs $ \ (Arg _ f) -> List.find (f ==) (toList ds) of
            [] -> refuseProjNoMatching ds
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
        [ "  principal arg " <+> prettyTCM arg
        , "  has type "      <+> prettyTCM ta
        ]
      inferOrCheckProjAppToKnownPrincipalArg e o ds args mt k v0 ta

-- | Same arguments 'inferOrCheckProjApp' above but also gets the position,
--   value and type of the principal argument.
inferOrCheckProjAppToKnownPrincipalArg ::
  A.Expr -> ProjOrigin -> NonemptyList QName -> A.Args -> Maybe (Comparison, Type) ->
  Int -> Term -> Type -> TCM (Term, Type, CheckedTarget)
inferOrCheckProjAppToKnownPrincipalArg e o ds args mt k v0 ta = do
  let cmp = caseMaybe mt CmpEq fst
      postpone m = do
        tc <- caseMaybe mt newTypeMeta_ (return . snd)
        v <- postponeTypeCheckingProblem (CheckProjAppToKnownPrincipalArg cmp e o ds args tc k v0 ta) $ isInstantiatedMeta m
        return (v, tc, NotCheckedTarget)
  -- ta should be a record type (after introducing the hidden args in v0)
  (vargs, ta) <- implicitArgs (-1) (not . visible) ta
  let v = v0 `apply` vargs
  ifBlocked ta (\ m _ -> postpone m) {-else-} $ \ _ ta -> do
  caseMaybeM (isRecordType ta) (refuseProjNotRecordType ds) $ \ (q, _pars0, _) -> do

      -- try to project it with all of the possible projections
      let try d = do
            reportSDoc "tc.proj.amb" 30 $ vcat
              [ text $ "trying projection " ++ prettyShow d
              , "  td  = " <+> caseMaybeM (getDefType d ta) "Nothing" prettyTCM
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
              [ "  dom = " <+> prettyTCM dom
              , "  u   = " <+> prettyTCM u
              , "  tb  = " <+> prettyTCM tb
              ]
            (q', pars, _) <- MaybeT $ isRecordType $ unDom dom
            reportSDoc "tc.proj.amb" 30 $ vcat
              [ "  q   = " <+> prettyTCM q
              , "  q'  = " <+> prettyTCM q'
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

            guard =<< do isNothing <$> do lift $ checkModality' d def
            return (orig, (d, (pars, (dom, u, tb))))

      cands <- groupOn fst . catMaybes <$> mapM (runMaybeT . try) (toList ds)
      case cands of
        [] -> refuseProjNoMatching ds
        [[]] -> refuseProjNoMatching ds
        (_:_:_) -> refuseProj ds $ "several matching candidates found: "
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
            Right (rs, us, trest, targetCheck) -> return (u `applyE` us, trest, targetCheck)
            Left problem -> do
              -- In the inference case:
              -- To create a postponed type checking problem,
              -- we do not use typeDontCare, but create a meta.
              tc <- caseMaybe mt newTypeMeta_ (return . snd)
              v  <- postponeArgs problem ExpandLast r args' tc $ \ rs us trest targetCheck ->
                      coerce' cmp targetCheck (u `applyE` us) trest tc

              return (v, tc, NotCheckedTarget)

refuseProj :: NonemptyList QName -> String -> TCM a
refuseProj ds reason = typeError $ GenericError $
        "Cannot resolve overloaded projection "
        ++ prettyShow (A.nameConcrete $ A.qnameName $ headNe ds)
        ++ " because " ++ reason

refuseProjNotApplied, refuseProjNoMatching, refuseProjNotRecordType :: NonemptyList QName -> TCM a
refuseProjNotApplied    ds = refuseProj ds "it is not applied to a visible argument"
refuseProjNoMatching    ds = refuseProj ds "no matching candidate found"
refuseProjNotRecordType ds = refuseProj ds "principal argument is not of record type"

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
    mod <- asksTC getModality
    abs <- asksTC (^. lensIsAbstract)
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
    -- If we are in erased position, add definition as erased.
    -- TODO: is this sufficient?
    addConstant c' =<< do
      let ai = setModality mod defaultArgInfo
      useTerPragma $
        (defaultDefn ai c' forcedType emptyFunction)
        { defMutual = i }

    checkFunDef NotDelayed info c' [clause]

    reportSDoc "tc.term.expr.coind" 15 $ do
      def <- theDef <$> getConstInfo c'
      vcat $
        [ "The coinductive wrapper"
        , nest 2 $ prettyTCM mod <> (prettyTCM c' <+> ":")
        , nest 4 $ prettyTCM t
        , nest 2 $ prettyA clause
        , ("The definition is" <+> text (show $ funDelayed def)) <>
          "."
        ]
    return c'

  -- The application of the fresh function to the relevant
  -- arguments.
  e' <- Def wrapper . map Apply <$> getContextArgs

  reportSDoc "tc.term.expr.coind" 15 $ vcat $
      [ "The coinductive constructor application"
      , nest 2 $ prettyTCM e
      , "was translated into the application"
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

-- | @primComp : ∀ {ℓ} (A : (i : I) → Set (ℓ i)) (φ : I) (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1@
--
--   Check:  @u i0 = (λ _ → a) : Partial φ (A i0)@.
--
checkPrimComp :: QName -> MaybeRanges -> Args -> Type -> TCM Args
checkPrimComp c rs vs _ = do
  case vs of
    -- WAS: [l, a, phi, u, a0] -> do
    l : a : phi : u : a0 : rest -> do
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      let lz = unArg l `apply` [iz]
          az = unArg a `apply` [iz]
      ty <- elInf $ primPartial <#> (pure $ unArg l `apply` [iz]) <@> (pure $ unArg phi) <@> (pure $ unArg a `apply` [iz])
      bAz <- el' (pure $ lz) (pure $ az)
      a0 <- blockArg bAz (rs !!! 4) a0 $ do
        equalTerm ty -- (El (getSort t1) (apply (unArg a) [iz]))
          (Lam defaultArgInfo $ NoAbs "_" $ unArg a0)
          (apply (unArg u) [iz])
      return $ l : a : phi : u : a0 : rest
    _ -> typeError $ GenericError $ show c ++ " must be fully applied"

-- | @primHComp : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A@
--
--   Check:  @u i0 = (λ _ → a) : Partial φ A@.
--
checkPrimHComp :: QName -> MaybeRanges -> Args -> Type -> TCM Args
checkPrimHComp c rs vs _ = do
  case vs of
    -- WAS: [l, a, phi, u, a0] -> do
    l : a : phi : u : a0 : rest -> do
      -- iz = i0
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      -- ty = Partial φ A
      ty <- elInf $ primPartial <#> (pure $ unArg l) <@> (pure $ unArg phi) <@> (pure $ unArg a)
      -- (λ _ → a) = u i0 : ty
      bA <- el' (pure $ unArg l) (pure $ unArg a)
      a0 <- blockArg bA (rs !!! 4) a0 $ do
        equalTerm ty -- (El (getSort t1) (apply (unArg a) [iz]))
            (Lam defaultArgInfo $ NoAbs "_" $ unArg a0)
            (apply (unArg u) [iz])
      return $ l : a : phi : u : a0 : rest
    _ -> typeError $ GenericError $ show c ++ " must be fully applied"

-- | @transp : ∀{ℓ} (A : (i : I) → Set (ℓ i)) (φ : I) (a0 : A i0) → A i1@
--
--   Check:  If φ, then @A i = A i0 : Set (ℓ i)@ must hold for all @i : I@.
--
checkPrimTrans :: QName -> MaybeRanges -> Args -> Type -> TCM Args
checkPrimTrans c rs vs _ = do
  case vs of
    -- Andreas, 2019-03-02, issue #3601, why exactly 4 arguments?
    -- Only 3 are needed to check the side condition.
    -- WAS:
    -- [l, a, phi, a0] -> do
    l : a : phi : rest -> do
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      -- ty = (i : I) -> Set (l i)
      ty <- runNamesT [] $ do
        l <- open $ unArg l
        nPi' "i" (elInf $ cl primInterval) $ \ i -> (sort . tmSort <$> (l <@> i))
      a <- blockArg ty (rs !!! 1) a $ do
        equalTermOnFace (unArg phi) ty
          (unArg a)
          (Lam defaultArgInfo $ NoAbs "_" $ apply (unArg a) [iz])
      return $ l : a : phi : rest
    _ -> typeError $ GenericError $ show c ++ " must be fully applied"

blockArg :: HasRange r => Type -> r -> Arg Term -> TCM () -> TCM (Arg Term)
blockArg t r a m =
  setCurrentRange (getRange $ r) $ fmap (a $>) $ blockTerm t $ m >> return (unArg a)

checkConId :: QName -> MaybeRanges -> Args -> Type -> TCM Args
checkConId c rs vs t1 = do
  case vs of
   args@[_, _, _, _, phi, p] -> do
      iv@(PathType s _ l a x y) <- idViewAsPath t1
      let ty = pathUnview iv
      -- the following duplicates reduction of phi
      const_x <- blockTerm ty $ do
          equalTermOnFace (unArg phi) (El s (unArg a)) (unArg x) (unArg y)
          pathAbs iv (NoAbs (stringToArgName "_") (unArg x))
      p <- blockArg ty (rs !!! 5) p $ do
        equalTermOnFace (unArg phi) ty (unArg p) const_x   -- G, phi |- p = \ i . x
      return $ init args ++ [p]
      -- phi <- reduce phi
      -- forallFaceMaps (unArg phi) $ \ alpha -> do
      --   iv@(PathType s _ l a x y) <- idViewAsPath (applySubst alpha t1)
      --   let ty = pathUnview iv
      --   equalTerm (El s (unArg a)) (unArg x) (unArg y) -- precondition for cx being well-typed at ty
      --   cx <- pathAbs iv (NoAbs (stringToArgName "_") (applySubst alpha (unArg x)))
      --   equalTerm ty (applySubst alpha (unArg p)) cx   -- G, phi |- p = \ i . x
   _ -> typeError $ GenericError $ show c ++ " must be fully applied"


-- The following comment contains silly ' escapes to calm CPP about ∨ (\vee).
-- May not be haddock-parseable.

-- ' @primPOr : ∀ {ℓ} (φ₁ φ₂ : I) {A : Partial (φ₁ ∨ φ₂) (Set ℓ)}
-- '         → (u : PartialP φ₁ (λ (o : IsOne φ₁) → A (IsOne1 φ₁ φ₂ o)))
-- '         → (v : PartialP φ₂ (λ (o : IsOne φ₂) → A (IsOne2 φ₁ φ₂ o)))
-- '         → PartialP (φ₁ ∨ φ₂) A@
-- '
-- ' Checks: @u = v : PartialP (φ₁ ∨ φ₂) A@ whenever @IsOne (φ₁ ∧ φ₂)@.
checkPOr :: QName -> MaybeRanges -> Args -> Type -> TCM Args
checkPOr c rs vs _ = do
  case vs of
   l : phi1 : phi2 : a : u : v : rest -> do
      phi <- intervalUnview (IMin phi1 phi2)
      reportSDoc "tc.term.por" 10 $ text (show phi)
      -- phi <- reduce phi
      -- alphas <- toFaceMaps phi
      -- reportSDoc "tc.term.por" 10 $ text (show alphas)
      t1 <- runNamesT [] $ do
             [l,a] <- mapM (open . unArg) [l,a]
             psi <- open =<< intervalUnview (IMax phi1 phi2)
             pPi' "o" psi $ \ o -> el' l (a <..> o)
      tv <- runNamesT [] $ do
             [l,a,phi1,phi2] <- mapM (open . unArg) [l,a,phi1,phi2]
             pPi' "o" phi2 $ \ o -> el' l (a <..> (cl primIsOne2 <@> phi1 <@> phi2 <@> o))
      v <- blockArg tv (rs !!! 5) v $ do
        -- ' φ₁ ∧ φ₂  ⊢ u , v : PartialP (φ₁ ∨ φ₂) \ o → a o
        equalTermOnFace phi t1 (unArg u) (unArg v)
      return $ l : phi1 : phi2 : a : u : v : rest
   _ -> typeError $ GenericError $ show c ++ " must be fully applied"

-- | @prim^glue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
--              → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
--              → (t : PartialP φ T) → (a : A) → primGlue A T e@
--
--   Check   @φ ⊢ a = e 1=1 (t 1=1)@  or actually the equivalent:  @(\ _ → a) = (\ o -> e o (t o)) : PartialP φ A@
check_glue :: QName -> MaybeRanges -> Args -> Type -> TCM Args
check_glue c rs vs _ = do
  case vs of
   -- WAS: [la, lb, bA, phi, bT, e, t, a] -> do
   la : lb : bA : phi : bT : e : t : a : rest -> do
      let iinfo = setRelevance Irrelevant defaultArgInfo
      v <- runNamesT [] $ do
            [lb, la, bA, phi, bT, e, t] <- mapM (open . unArg) [lb, la, bA, phi, bT, e, t]
            let f o = cl primEquivFun <#> lb <#> la <#> (bT <..> o) <#> bA <@> (e <..> o)
            glam iinfo "o" $ \ o -> f o <@> (t <..> o)
      ty <- runNamesT [] $ do
            [lb, phi, bA] <- mapM (open . unArg) [lb, phi, bA]
            elInf $ cl primPartialP <#> lb <@> phi <@> (glam iinfo "o" $ \ _ -> bA)
      let a' = Lam iinfo (NoAbs "o" $ unArg a)
      ta <- el' (pure $ unArg la) (pure $ unArg bA)
      a <- blockArg ta (rs !!! 7) a $ equalTerm ty a' v
      return $ la : lb : bA : phi : bT : e : t : a : rest
   _ -> typeError $ GenericError $ show c ++ " must be fully applied"


-- | @prim^glueU : ∀ {ℓ} {φ : I}
--              → {T : I → Partial φ (Set ℓ)} → {A : Set ℓ [ φ ↦ T i0 ]}
--              → (t : PartialP φ (T i1)) → (a : outS A) → hcomp T (outS A)@
--
--   Check   @φ ⊢ a = transp (\ i -> T 1=1 (~ i)) i0 (t 1=1)@  or actually the equivalent:
--           @(\ _ → a) = (\o -> transp (\ i -> T o (~ i)) i0 (t o)) : PartialP φ (T i0)@
check_glueU :: QName -> MaybeRanges -> Args -> Type -> TCM Args
check_glueU c rs vs _ = do
  case vs of
   -- WAS: [la, lb, bA, phi, bT, e, t, a] -> do
   la : phi : bT : bA : t : a : rest -> do
      let iinfo = setRelevance Irrelevant defaultArgInfo
      v <- runNamesT [] $ do
            [la, phi, bT, bA, t] <- mapM (open . unArg) [la, phi, bT, bA, t]
            let f o = cl primTrans <#> (lam "i" $ const la) <@> (lam "i" $ \ i -> bT <@> (cl primINeg <@> i) <..> o) <@> cl primIZero
            glam iinfo "o" $ \ o -> f o <@> (t <..> o)
      ty <- runNamesT [] $ do
            [la, phi, bT] <- mapM (open . unArg) [la, phi, bT]
            pPi' "o" phi $ \ o -> el' la (bT <@> cl primIZero <..> o)
      let a' = Lam iinfo (NoAbs "o" $ unArg a)
      ta <- runNamesT [] $ do
            [la, phi, bT, bA] <- mapM (open . unArg) [la, phi, bT, bA]
            el' la (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <#> (bT <@> cl primIZero) <@> bA)
      a <- blockArg ta (rs !!! 5) a $ equalTerm ty a' v
      return $ la : phi : bT : bA : t : a : rest
   _ -> typeError $ GenericError $ show c ++ " must be fully applied"
