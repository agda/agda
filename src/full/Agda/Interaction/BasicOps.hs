{-# LANGUAGE NondecreasingIndentation #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Interaction.BasicOps where

import Prelude hiding (null)

import Control.Arrow          ( first )
import Control.Monad          ( (<=<), (>=>), forM, filterM, guard )
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Trans.Maybe

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Maybe
import Data.Monoid
import Data.Function (on)
import Data.Text (Text)
import qualified Data.Text as T

import Agda.Interaction.Base
import Agda.Interaction.Options
import Agda.Interaction.Response (Goals, ResponseContextEntry(..))

import qualified Agda.Syntax.Concrete as C -- ToDo: Remove with instance of ToConcrete
import Agda.Syntax.Position
import Agda.Syntax.Abstract as A hiding (Open, Apply, Assign)
import Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Info (MetaInfo(..),emptyMetaInfo,exprNoRange,defaultAppInfo_,defaultAppInfo)
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Fixity(Precedence(..), argumentCtx_)
import Agda.Syntax.Parser

import Agda.TheTypeChecker
import Agda.TypeChecking.ReconstructParameters
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Errors ( getAllWarnings, stringTCErr, Verbalize(..) )
import Agda.TypeChecking.Monad as M hiding (MetaInfo)
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.With
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Coverage.Match ( SplitPattern )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty ( PrettyTCM, prettyTCM )
import Agda.TypeChecking.Pretty.Constraint (prettyRangeConstraint)
import Agda.TypeChecking.IApplyConfluence
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Names
import Agda.TypeChecking.Free
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.SizedTypes.Solve
import qualified Agda.TypeChecking.Pretty as TP
import Agda.TypeChecking.Warnings
  ( runPM, warning, WhichWarnings(..), classifyWarnings, isMetaTCWarning
  , WarningsAndNonFatalErrors, emptyWarningsAndNonFatalErrors )

import Agda.Termination.TermCheck (termMutual)

import Agda.Utils.Function (applyWhen)
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty as P
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.String

import Agda.Utils.Impossible
import qualified Agda.Utils.SmallSet as SmallSet
import Agda.TypeChecking.ProjectionLike (reduceProjectionLike)

-- | Parses an expression.

parseExpr :: Range -> String -> TCM C.Expr
parseExpr rng s = do
  (C.ExprWhere e wh, attrs) <-
    runPM $ parsePosString exprWhereParser pos s
  checkAttributes attrs
  unless (null wh) $ typeError $ GenericError $
    "where clauses are not supported in holes"
  return e
  where pos = fromMaybe (startPos Nothing) $ rStart rng

parseExprIn :: InteractionId -> Range -> String -> TCM Expr
parseExprIn ii rng s = do
    mId <- lookupInteractionId ii
    updateMetaVarRange mId rng
    mi  <- getMetaInfo <$> lookupLocalMeta mId
    e   <- parseExpr rng s
    -- Andreas, 2019-08-19, issue #4007
    -- We need to be in the TCEnv of the meta variable
    -- such that the scope checker can label the clause
    -- of a parsed extended lambda as IsAbstract if the
    -- interaction point was created in AbstractMode.
    withMetaInfo mi $
      concreteToAbstract (clScope mi) e

-- Type check the given expression and assign its value to the meta
-- Precondition: we are in the context where the given meta was created.
giveExpr :: UseForce -> Maybe InteractionId -> MetaId -> Expr -> TCM Term
giveExpr force mii mi e = do
    mv <- lookupLocalMeta mi
    let t = case mvJudgement mv of
              IsSort{}    -> __IMPOSSIBLE__
              HasType _ _ t -> t
    reportSDoc "interaction.give" 20 $
      "give: meta type =" TP.<+> prettyTCM t
    -- Here, we must be in the same context where the meta was created.
    -- Thus, we can safely apply its type to the context variables.
    ctx <- getContextArgs
    t' <- t `piApplyM` permute (takeP (length ctx) $ mvPermutation mv) ctx
    traceCall (CheckExprCall CmpLeq e t') $ do
      reportSDoc "interaction.give" 20 $ do
        a <- asksTC envAbstractMode
        TP.hsep
          [ TP.text ("give(" ++ show a ++ "): instantiated meta type =")
          , prettyTCM t'
          ]
      -- Andreas, 2020-05-27 AIM XXXII, issue #4679
      -- Clear envMutualBlock since cubical only executes
      -- certain checks (checkIApplyConfluence) for an extended lambda
      -- when not in a mutual block.
      v <- locallyTC eMutualBlock (const Nothing) $
        checkExpr e t'
      reportSDoc "interaction.give" 40 $ "give: checked expression:" TP.<+> pure (pretty v)
      case mvInstantiation mv of

        InstV{} -> unlessM ((Irrelevant ==) <$> viewTC eRelevance) $ do
          v' <- instantiate $ MetaV mi $ map Apply ctx
          reportSDoc "interaction.give" 20 $ TP.sep
            [ "meta was already set to value v' = " TP.<+> prettyTCM v'
            , "now comparing it to given value v = " TP.<+> prettyTCM v
            , "in context " TP.<+> inTopContext (prettyTCM ctx)
            ]
          equalTerm t' v v'

        _ -> do -- updateMeta mi v
          reportSLn "interaction.give" 20 "give: meta unassigned, assigning..."
          args <- getContextArgs
          nowSolvingConstraints $ assign DirEq mi args v (AsTermsOf t')

      reportSDoc "interaction.give" 20 $ "give: meta variable updated!"
      unless (force == WithForce) $ redoChecks mii
      wakeupConstraints mi
      solveSizeConstraints DontDefaultToInfty
      cubical <- isJust . optCubical <$> pragmaOptions
      -- don't double check with cubical, because it gets in the way too often.
      unless (cubical || force == WithForce) $ do
        -- Double check.
        reportSDoc "interaction.give" 20 $ "give: double checking"
        vfull <- instantiateFull v
        checkInternal vfull CmpLeq t'
      return v

-- | After a give, redo termination etc. checks for function which was complemented.
redoChecks :: Maybe InteractionId -> TCM ()
redoChecks Nothing = return ()
redoChecks (Just ii) = do
  reportSLn "interaction.give" 20 $
    "give: redoing termination check for function surrounding " ++ show ii
  ip <- lookupInteractionPoint ii
  case ipClause ip of
    IPNoClause -> return ()
    IPClause{ipcQName = f} -> do
      mb <- mutualBlockOf f
      terErrs <- localTC (\ e -> e { envMutualBlock = Just mb }) $ termMutual []
      unless (null terErrs) $ warning $ TerminationIssue terErrs
  -- TODO redo positivity check!

-- | Try to fill hole by expression.
--
--   Returns the given expression unchanged
--   (for convenient generalization to @'refine'@).
give
  :: UseForce       -- ^ Skip safety checks?
  -> InteractionId  -- ^ Hole.
  -> Maybe Range
  -> Expr           -- ^ The expression to give.
  -> TCM Expr       -- ^ If successful, the very expression is returned unchanged.
give force ii mr e = liftTCM $ do
  -- if Range is given, update the range of the interaction meta
  mi  <- lookupInteractionId ii
  whenJust mr $ updateMetaVarRange mi
  reportSDoc "interaction.give" 10 $ "giving expression" TP.<+> prettyTCM e
  reportSDoc "interaction.give" 50 $ TP.text $ show $ deepUnscope e
  -- Try to give mi := e
  _ <- withInteractionId ii $ do
     setMetaOccursCheck mi DontRunMetaOccursCheck -- #589, #2710: Allow giving recursive solutions.
     giveExpr force (Just ii) mi e
    `catchError` \ case
      -- Turn PatternErr into proper error:
      PatternErr{} -> typeError . GenericDocError =<< do
        withInteractionId ii $ "Failed to give" TP.<+> prettyTCM e
      err -> throwError err
  removeInteractionPoint ii
  return e

-- | Try to fill hole by elaborated expression.
elaborate_give
  :: Rewrite        -- ^ Normalise result?
  -> UseForce       -- ^ Skip safety checks?
  -> InteractionId  -- ^ Hole.
  -> Maybe Range
  -> Expr           -- ^ The expression to give.
  -> TCM Expr       -- ^ If successful, return the elaborated expression.
elaborate_give norm force ii mr e = withInteractionId ii $ do
  -- if Range is given, update the range of the interaction meta
  mi  <- lookupInteractionId ii
  whenJust mr $ updateMetaVarRange mi
  reportSDoc "interaction.give" 10 $ "giving expression" TP.<+> prettyTCM e
  reportSDoc "interaction.give" 50 $ TP.text $ show $ deepUnscope e
  -- Try to give mi := e
  v <- withInteractionId ii $ do
     setMetaOccursCheck mi DontRunMetaOccursCheck -- #589, #2710: Allow giving recursive solutions.
     locallyTC eCurrentlyElaborating (const True) $
       giveExpr force (Just ii) mi e
    `catchError` \ case
      -- Turn PatternErr into proper error:
      PatternErr{} -> typeError . GenericDocError =<< do
        withInteractionId ii $ "Failed to give" TP.<+> prettyTCM e
      err -> throwError err
  mv <- lookupLocalMeta mi
  -- Reduce projection-likes before quoting, otherwise instance
  -- selection may fail on reload (see #6203).
  nv <- reduceProjectionLike =<< normalForm norm v
  reportSDoc "interaction.give" 40 $ "nv = " TP.<+> pure (pretty v)
  locallyTC ePrintMetasBare (const True) $ reify nv

-- | Try to refine hole by expression @e@.
--
--   This amounts to successively try to give @e@, @e ?@, @e ? ?@, ...
--   Returns the successfully given expression.
refine
  :: UseForce       -- ^ Skip safety checks when giving?
  -> InteractionId  -- ^ Hole.
  -> Maybe Range
  -> Expr           -- ^ The expression to refine the hole with.
  -> TCM Expr       -- ^ The successfully given expression.
refine force ii mr e = do
  mi <- lookupInteractionId ii
  mv <- lookupLocalMeta mi
  let range = fromMaybe (getRange mv) mr
      scope = M.getMetaScope mv
  reportSDoc "interaction.refine" 10 $
    "refining with expression" TP.<+> prettyTCM e
  reportSDoc "interaction.refine" 50 $
    TP.text $ show $ deepUnscope e
  -- We try to append up to 10 meta variables
  tryRefine 10 range scope e
  where
    tryRefine :: Int -> Range -> ScopeInfo -> Expr -> TCM Expr
    tryRefine nrOfMetas r scope = try nrOfMetas Nothing
      where
        try :: Int -> Maybe TCErr -> Expr -> TCM Expr
        try 0 err e = throwError . stringTCErr $ case err of
           Just (TypeError _ _ cl) | UnequalTerms _ I.Pi{} _ _ <- clValue cl ->
             "Cannot refine functions with 10 or more arguments"
           _ ->
             "Cannot refine"
        try n _ e = give force ii (Just r) e `catchError` \err -> try (n - 1) (Just err) =<< appMeta e

        -- Apply A.Expr to a new meta
        appMeta :: Expr -> TCM Expr
        appMeta e = do
          let rng = rightMargin r -- Andreas, 2013-05-01 conflate range to its right margin to ensure that appended metas are last in numbering.  This fixes issue 841.
          -- Make new interaction point
          ii <- registerInteractionPoint False rng Nothing
          let info = Info.MetaInfo
                { Info.metaRange = rng
                , Info.metaScope = set scopePrecedence [argumentCtx_] scope
                    -- Ulf, 2017-09-07: The `argumentCtx_` above is causing #737.
                    -- If we're building an operator application the precedence
                    -- should be something else.
                , metaNumber = Nothing -- in order to print just as ?, not ?n
                , metaNameSuggestion = ""
                }
              metaVar = QuestionMark info ii

              count x e = getSum $ foldExpr isX e
                where isX (A.Var y) | x == y = Sum 1
                      isX _                  = mempty

              lamView (A.Lam _ (DomainFree _ x) e) = Just (namedArg x, e)
              lamView (A.Lam i (DomainFull (TBind r t (x :| xs) a)) e) =
                List1.ifNull xs {-then-} (Just (namedArg x, e)) {-else-} $ \ xs ->
                  Just (namedArg x, A.Lam i (DomainFull $ TBind r t xs a) e)
              lamView _ = Nothing

              -- reduce beta-redexes where the argument is used at most once
              smartApp i e arg =
                case fmap (first A.binderName) (lamView $ unScope e) of
                  Just (A.BindName{unBind = x}, e) | count x e < 2 -> mapExpr subX e
                    where subX (A.Var y) | x == y = namedArg arg
                          subX e = e
                  _ -> App i e arg
          return $ smartApp (defaultAppInfo r) e $ defaultNamedArg metaVar

-- Andreas, 2017-12-16:
-- Ulf, your attempt to fix #737 introduced regression #2873.
-- Going through concrete syntax does some arbitrary disambiguation
-- of constructors, which subsequently makes refine fail.
-- I am not convinced of the printing-parsing shortcut to address problems.
-- (Unless you prove the roundtrip property.)
--
--           rescopeExpr scope $ smartApp (defaultAppInfo r) e $ defaultNamedArg metaVar
-- -- | Turn an abstract expression into concrete syntax and then back into
-- --   abstract. This ensures that context precedences are set correctly for
-- --   abstract expressions built by hand. Used by refine above.
-- rescopeExpr :: ScopeInfo -> Expr -> TCM Expr
-- rescopeExpr scope = withScope_ scope . (concreteToAbstract_ <=< runAbsToCon . preserveInteractionIds . toConcrete)

{-| Evaluate the given expression in the current environment -}
evalInCurrent :: ComputeMode -> Expr -> TCM Expr
evalInCurrent cmode e = do
  (v, _t) <- inferExpr e
  reify =<< compute v
  where compute | cmode == HeadCompute = reduce
                | otherwise            = normalise


evalInMeta :: InteractionId -> ComputeMode -> Expr -> TCM Expr
evalInMeta ii cmode e =
   do   m <- lookupInteractionId ii
        mi <- getMetaInfo <$> lookupLocalMeta m
        withMetaInfo mi $
            evalInCurrent cmode e

-- | Modifier for interactive commands,
--   specifying the amount of normalization in the output.
--
normalForm :: (Reduce t, Simplify t, Instantiate t, Normalise t) => Rewrite -> t -> TCM t
normalForm = \case
  AsIs         -> instantiate   -- #4975: reify will also instantiate by for goal-type-and-context-and-check
  Instantiated -> instantiate   --        we get a top-level fresh meta which has disappeared from state by the
  HeadNormal   -> reduce        --        time we get to reification. Hence instantiate here.
  Simplified   -> simplify
  Normalised   -> normalise

-- | Modifier for the interactive computation command,
--   specifying the mode of computation and result display.
--
computeIgnoreAbstract :: ComputeMode -> Bool
computeIgnoreAbstract DefaultCompute  = False
computeIgnoreAbstract HeadCompute     = False
computeIgnoreAbstract IgnoreAbstract  = True
computeIgnoreAbstract UseShowInstance = True
  -- UseShowInstance requires the result to be a string literal so respecting
  -- abstract can only ever break things.

computeWrapInput :: ComputeMode -> String -> String
computeWrapInput UseShowInstance s = "show (" ++ s ++ ")"
computeWrapInput _               s = s

showComputed :: ComputeMode -> Expr -> TCM Doc
showComputed UseShowInstance e =
  case e of
    A.Lit _ (LitString s) -> pure (text $ T.unpack s)
    _                     -> ("Not a string:" $$) <$> prettyATop e
showComputed _ e = prettyATop e

-- | Modifier for interactive commands,
--   specifying whether safety checks should be ignored.
outputFormId :: OutputForm a b -> b
outputFormId (OutputForm _ _ _ o) = out o
  where
    out = \case
      OfType i _                 -> i
      CmpInType _ _ i _          -> i
      CmpElim _ _ (i:_) _        -> i
      CmpElim _ _ [] _           -> __IMPOSSIBLE__
      JustType i                 -> i
      CmpLevels _ i _            -> i
      CmpTypes _ i _             -> i
      CmpTeles _ i _             -> i
      JustSort i                 -> i
      CmpSorts _ i _             -> i
      Assign i _                 -> i
      TypedAssign i _ _          -> i
      PostponedCheckArgs i _ _ _ -> i
      IsEmptyType _              -> __IMPOSSIBLE__   -- Should never be used on IsEmpty constraints
      SizeLtSat{}                -> __IMPOSSIBLE__
      FindInstanceOF _ _ _        -> __IMPOSSIBLE__
      PTSInstance i _            -> i
      PostponedCheckFunDef{}     -> __IMPOSSIBLE__
      DataSort _ i               -> i
      CheckLock i _              -> i
      UsableAtMod _ i            -> i

instance Reify ProblemConstraint where
  type ReifiesTo ProblemConstraint = Closure (OutputForm Expr Expr)
  reify (PConstr pids unblock cl) = withClosure cl $ \ c ->
    OutputForm (getRange c) (Set.toList pids) unblock <$> reify c

reifyElimToExpr :: MonadReify m => I.Elim -> m Expr
reifyElimToExpr = \case
    I.IApply _ _ v -> appl "iapply" <$> reify (defaultArg $ v) -- TODO Andrea: endpoints?
    I.Apply v -> appl "apply" <$> reify v
    I.Proj _o f -> appl "proj" <$> reify ((defaultArg $ I.Def f []) :: Arg Term)
  where
    appl :: Text -> Arg Expr -> Expr
    appl s v = A.App defaultAppInfo_ (A.Lit empty (LitString s)) $ fmap unnamed v

instance Reify Constraint where
    type ReifiesTo Constraint = OutputConstraint Expr Expr

    reify (ValueCmp cmp (AsTermsOf t) u v) = CmpInType cmp <$> reify t <*> reify u <*> reify v
    reify (ValueCmp cmp AsSizes u v) = CmpInType cmp <$> (reify =<< sizeType) <*> reify u <*> reify v
    reify (ValueCmp cmp AsTypes u v) = CmpTypes cmp <$> reify u <*> reify v
    reify (ValueCmpOnFace cmp p t u v) = CmpInType cmp <$> (reify =<< ty) <*> reify (lam_o u) <*> reify (lam_o v)
      where
        lam_o = I.Lam (setRelevance Irrelevant defaultArgInfo) . NoAbs "_"
        ty = runNamesT [] $ do
          p <- open p
          t <- open t
          pPi' "o" p (\ o -> t)
    reify (ElimCmp cmp _ t v es1 es2) =
      CmpElim cmp <$> reify t <*> mapM reifyElimToExpr es1
                              <*> mapM reifyElimToExpr es2
    reify (LevelCmp cmp t t')    = CmpLevels cmp <$> reify t <*> reify t'
    reify (SortCmp cmp s s')     = CmpSorts cmp <$> reify s <*> reify s'
    reify (UnquoteTactic tac _ goal) = do
        tac <- A.App defaultAppInfo_ (A.Unquote exprNoRange) . defaultNamedArg <$> reify tac
        OfType tac <$> reify goal
    reify (UnBlock m) = do
        mi <- lookupMetaInstantiation m
        m' <- reify (MetaV m [])
        case mi of
          BlockedConst t -> do
            e  <- reify t
            return $ Assign m' e
          PostponedTypeCheckingProblem cl -> enterClosure cl $ \case
            CheckExpr cmp e a -> do
                a  <- reify a
                return $ TypedAssign m' e a
            CheckLambda cmp (Arg ai (xs, mt)) body target -> do
              domType <- maybe (return underscore) reify mt
              target  <- reify target
              let mkN (WithHiding h x) = setHiding h $ defaultNamedArg $ A.mkBinder_ x
                  bs = mkTBind noRange (fmap mkN xs) domType
                  e  = A.Lam Info.exprNoRange (DomainFull bs) body
              return $ TypedAssign m' e target
            CheckArgs _ _ _ args t0 t1 _ -> do
              t0 <- reify t0
              t1 <- reify t1
              return $ PostponedCheckArgs m' (map (namedThing . unArg) args) t0 t1
            CheckProjAppToKnownPrincipalArg cmp e _ _ _ t _ _ _ _ -> TypedAssign m' e <$> reify t
            DoQuoteTerm cmp v t -> do
              tm <- A.App defaultAppInfo_ (A.QuoteTerm exprNoRange) . defaultNamedArg <$> reify v
              OfType tm <$> reify t
          Open{}  -> __IMPOSSIBLE__
          OpenInstance{}  -> __IMPOSSIBLE__
          InstV{} -> __IMPOSSIBLE__
    reify (FindInstance m mcands) = FindInstanceOF
      <$> reify (MetaV m [])
      <*> (reify =<< getMetaType m)
      <*> forM (fromMaybe [] mcands) (\ (Candidate q tm ty _) -> do
            (,,) <$> reify tm <*> reify tm <*> reify ty)
    reify (IsEmpty r a) = IsEmptyType <$> reify a
    reify (CheckSizeLtSat a) = SizeLtSat  <$> reify a
    reify (CheckFunDef d i q cs err) = do
      a <- reify =<< defType <$> getConstInfo q
      return $ PostponedCheckFunDef q a err
    reify (HasBiggerSort a) = OfType <$> reify a <*> reify (UnivSort a)
    reify (HasPTSRule a b) = do
      (a,(x,b)) <- reify (unDom a,b)
      return $ PTSInstance a b
    reify (CheckDataSort q s) = DataSort q <$> reify s
    reify (CheckLockedVars t _ lk _) = CheckLock <$> reify t <*> reify (unArg lk)
    reify (CheckMetaInst m) = do
      t <- jMetaType . mvJudgement <$> lookupLocalMeta m
      OfType <$> reify (MetaV m []) <*> reify t
    reify (CheckType t) = JustType <$> reify t
    reify (UsableAtModality _ _ mod t) = UsableAtMod mod <$> reify t

instance (Pretty a, Pretty b) => PrettyTCM (OutputForm a b) where
  prettyTCM (OutputForm r pids unblock c) =
    prettyRangeConstraint r pids unblock (pretty c)

instance (Pretty a, Pretty b) => Pretty (OutputForm a b) where
  pretty (OutputForm r pids unblock c) =
    pretty c <?>
      sep [ prange r, parensNonEmpty (sep [blockedOn unblock, prPids pids]) ]
    where
      prPids []    = empty
      prPids [pid] = "belongs to problem" <+> pretty pid
      prPids pids  = "belongs to problems" <+> fsep (punctuate "," $ map pretty pids)

      comma | null pids = empty
            | otherwise = ","

      blockedOn (UnblockOnAll bs) | Set.null bs = empty
      blockedOn (UnblockOnAny bs) | Set.null bs = "stuck" P.<> comma
      blockedOn u = "blocked on" <+> (pretty u P.<> comma)

      prange r | null s = empty
               | otherwise = text $ " [ at " ++ s ++ " ]"
        where s = prettyShow r

instance (Pretty a, Pretty b) => Pretty (OutputConstraint a b) where
  pretty oc =
    case oc of
      OfType e t           -> pretty e .: t
      JustType e           -> "Type" <+> pretty e
      JustSort e           -> "Sort" <+> pretty e
      CmpInType cmp t e e' -> pcmp cmp e e' .: t
      CmpElim cmp t e e'   -> pcmp cmp e e' .: t
      CmpTypes  cmp t t'   -> pcmp cmp t t'
      CmpLevels cmp t t'   -> pcmp cmp t t'
      CmpTeles  cmp t t'   -> pcmp cmp t t'
      CmpSorts cmp s s'    -> pcmp cmp s s'
      Assign m e           -> bin (pretty m) ":=" (pretty e)
      TypedAssign m e a    -> bin (pretty m) ":=" $ bin (pretty e) ":?" (pretty a)
      PostponedCheckArgs m es t0 t1 ->
        bin (pretty m) ":=" $ (parens ("_" .: t0) <+> fsep (map (paren . pretty) es)) .: t1
        where paren d = mparens (any (`elem` [' ', '\n']) $ show d) d
      IsEmptyType a        -> "Is empty:" <+> pretty a
      SizeLtSat a          -> "Not empty type of sizes:" <+> pretty a
      FindInstanceOF s t cs -> vcat
        [ "Resolve instance argument" <?> (pretty s .: t)
        , nest 2 $ "Candidate:"
        , nest 4 $ vcat [ bin (pretty q) "=" (pretty v) .: t | (q, v, t) <- cs ] ]
      PTSInstance a b      -> "PTS instance for" <+> pretty (a, b)
      PostponedCheckFunDef q a _err ->
        vcat [ "Check definition of" <+> pretty q <+> ":" <+> pretty a ]
             -- , nest 2 "stuck because" <?> pretty err ] -- We don't have Pretty for TCErr
      DataSort q s         -> "Sort" <+> pretty s <+> "allows data/record definitions"
      CheckLock t lk       -> "Check lock" <+> pretty lk <+> "allows" <+> pretty t
      UsableAtMod mod t    -> "Is usable at" <+> text (verbalize mod) <+> "modality:" <+> pretty t
    where
      bin a op b = sep [a, nest 2 $ op <+> b]
      pcmp cmp a b = bin (pretty a) (pretty cmp) (pretty b)
      val .: ty = bin val ":" (pretty ty)


instance (ToConcrete a, ToConcrete b) => ToConcrete (OutputForm a b) where
    type ConOfAbs (OutputForm a b) = OutputForm (ConOfAbs a) (ConOfAbs b)
    toConcrete (OutputForm r pid u c) = OutputForm r pid u <$> toConcrete c

instance (ToConcrete a, ToConcrete b) => ToConcrete (OutputConstraint a b) where
    type ConOfAbs (OutputConstraint a b) = OutputConstraint (ConOfAbs a) (ConOfAbs b)

    toConcrete (OfType e t) = OfType <$> toConcrete e <*> toConcreteCtx TopCtx t
    toConcrete (JustType e) = JustType <$> toConcrete e
    toConcrete (JustSort e) = JustSort <$> toConcrete e
    toConcrete (CmpInType cmp t e e') =
      CmpInType cmp <$> toConcreteCtx TopCtx t <*> toConcreteCtx TopCtx e
                                               <*> toConcreteCtx TopCtx e'
    toConcrete (CmpElim cmp t e e') =
      CmpElim cmp <$> toConcreteCtx TopCtx t <*> toConcreteCtx TopCtx e <*> toConcreteCtx TopCtx e'
    toConcrete (CmpTypes cmp e e') = CmpTypes cmp <$> toConcreteCtx TopCtx e
                                                  <*> toConcreteCtx TopCtx e'
    toConcrete (CmpLevels cmp e e') = CmpLevels cmp <$> toConcreteCtx TopCtx e
                                                    <*> toConcreteCtx TopCtx e'
    toConcrete (CmpTeles cmp e e') = CmpTeles cmp <$> toConcrete e <*> toConcrete e'
    toConcrete (CmpSorts cmp e e') = CmpSorts cmp <$> toConcreteCtx TopCtx e
                                                  <*> toConcreteCtx TopCtx e'
    toConcrete (Assign m e) = noTakenNames $ Assign <$> toConcrete m <*> toConcreteCtx TopCtx e
    toConcrete (TypedAssign m e a) = TypedAssign <$> toConcrete m <*> toConcreteCtx TopCtx e
                                                                  <*> toConcreteCtx TopCtx a
    toConcrete (PostponedCheckArgs m args t0 t1) =
      PostponedCheckArgs <$> toConcrete m <*> toConcrete args <*> toConcrete t0 <*> toConcrete t1
    toConcrete (IsEmptyType a) = IsEmptyType <$> toConcreteCtx TopCtx a
    toConcrete (SizeLtSat a) = SizeLtSat <$> toConcreteCtx TopCtx a
    toConcrete (FindInstanceOF s t cs) =
      FindInstanceOF <$> toConcrete s <*> toConcrete t
                     <*> mapM (\(q,tm,ty) -> (,,) <$> toConcrete q <*> toConcrete tm <*> toConcrete ty) cs
    toConcrete (PTSInstance a b) = PTSInstance <$> toConcrete a <*> toConcrete b
    toConcrete (DataSort a b)  = DataSort a <$> toConcrete b
    toConcrete (CheckLock a b) = CheckLock <$> toConcrete a <*> toConcrete b
    toConcrete (PostponedCheckFunDef q a err) = PostponedCheckFunDef q <$> toConcrete a <*> pure err
    toConcrete (UsableAtMod a b) = UsableAtMod a <$> toConcrete b

instance (Pretty a, Pretty b) => Pretty (OutputConstraint' a b) where
  pretty (OfType' e t) = pretty e <+> ":" <+> pretty t

instance (ToConcrete a, ToConcrete b) => ToConcrete (OutputConstraint' a b) where
  type ConOfAbs (OutputConstraint' a b) = OutputConstraint' (ConOfAbs a) (ConOfAbs b)
  toConcrete (OfType' e t) = OfType' <$> toConcrete e <*> toConcreteCtx TopCtx t

instance Reify a => Reify (IPBoundary' a) where
  type ReifiesTo (IPBoundary' a) = IPBoundary' (ReifiesTo a)
  reify = traverse reify

instance ToConcrete a => ToConcrete (IPBoundary' a) where
  type ConOfAbs (IPBoundary' a) = IPBoundary' (ConOfAbs a)

  toConcrete = traverse (toConcreteCtx TopCtx)

instance Pretty c => Pretty (IPFace' c) where
  pretty (IPFace' eqs val) = do
    let
      xs = map (\ (l,r) -> pretty l <+> "=" <+> pretty r) eqs
      -- rhs = case over of
      --         Overapplied    -> "=" <+> pretty meta
      --         NotOverapplied -> mempty
    prettyList_ xs <+> "⊢" <+> pretty val -- <+> rhs

prettyConstraints :: [Closure Constraint] -> TCM [OutputForm C.Expr C.Expr]
prettyConstraints cs = do
  forM cs $ \ c -> do
            cl <- reify (PConstr Set.empty alwaysUnblock c)
            enterClosure cl abstractToConcrete_

getConstraints :: TCM [OutputForm C.Expr C.Expr]
getConstraints = getConstraints' return $ const True

namedMetaOf :: OutputConstraint A.Expr a -> a
namedMetaOf (OfType i _) = i
namedMetaOf (JustType i) = i
namedMetaOf (JustSort i) = i
namedMetaOf (Assign i _) = i
namedMetaOf _ = __IMPOSSIBLE__

getConstraintsMentioning :: Rewrite -> MetaId -> TCM [OutputForm C.Expr C.Expr]
getConstraintsMentioning norm m = getConstrs instantiateBlockingFull (mentionsMeta m)
  -- could be optimized by not doing a full instantiation up front, with a more clever mentionsMeta.
  where
    instantiateBlockingFull p
      = locallyTCState stInstantiateBlocking (const True) $
          instantiateFull p

    nay :: MaybeT TCM Elims
    nay = MaybeT $ pure Nothing

    -- Trying to find the actual meta application, as long as it's not
    -- buried too deep.
    -- We could look further but probably not under binders as that would mess with
    -- the call to @unifyElimsMeta@ below.
    hasHeadMeta c =
      case c of
        ValueCmp _ _ u v           -> isMeta u `mplus` isMeta v
        ValueCmpOnFace cmp p t u v -> isMeta u `mplus` isMeta v
        -- TODO: extend to other comparisons?
        ElimCmp cmp fs t v as bs   -> Nothing
        LevelCmp cmp u v           -> Nothing
        SortCmp cmp a b            -> Nothing
        UnBlock{}                  -> Nothing
        FindInstance{}             -> Nothing
        IsEmpty r t                -> isMeta (unEl t)
        CheckSizeLtSat t           -> isMeta t
        CheckFunDef{}              -> Nothing
        HasBiggerSort a            -> Nothing
        HasPTSRule a b             -> Nothing
        UnquoteTactic{}            -> Nothing
        CheckDataSort _ s          -> isMetaS s
        CheckMetaInst{}            -> Nothing
        CheckType t                -> isMeta (unEl t)
        CheckLockedVars t _ _ _    -> isMeta t
        UsableAtModality _ ms _ t  -> caseMaybe ms (isMeta t) $ \ s -> isMetaS s `mplus` isMeta t

    isMeta :: Term -> Maybe Elims
    isMeta (MetaV m' es_m) | m == m' = pure es_m
    isMeta _  = Nothing

    isMetaS :: I.Sort -> Maybe Elims
    isMetaS (MetaS m' es_m)
      | m == m' = pure es_m
    isMetaS _  = Nothing

    getConstrs g f = liftTCM $ do
      cs <- stripConstraintPids . filter f <$> (mapM g =<< M.getAllConstraints)
      cs <- caseMaybeM (traverse lookupInteractionPoint =<< isInteractionMeta m) (pure cs) $ \ip -> do
        let
          boundary = MapS.keysSet (getBoundary (ipBoundary ip))
          isRedundant c = case allApplyElims =<< hasHeadMeta c of
            Just apps -> caseMaybeM (isFaceConstraint m apps) (pure False) $ \(_, endps, _, _) ->
              pure $ Set.member endps boundary
            Nothing -> pure False
        filterM (flip enterClosure (fmap not . isRedundant) . theConstraint) cs

      reportSDoc "tc.constr.mentioning" 20 $ "getConstraintsMentioning"
      forM cs $ \(PConstr s ub c) -> do
        reportSDoc "tc.constr.mentioning" 20 $ "constraint:  " TP.<+> prettyTCM c
        c <- normalForm norm c
        let hm = hasHeadMeta (clValue c)
        reportSDoc "tc.constr.mentioning" 20 $ "constraint:  " TP.<+> prettyTCM c
        reportSDoc "tc.constr.mentioning" 20 $ "hasHeadMeta: " TP.<+> prettyTCM hm
        case allApplyElims =<< hm of
          Just as_m -> do
            -- unifyElimsMeta tries to move the constraint into
            -- (an extension of) the context where @m@ comes from.
            unifyElimsMeta m as_m c $ \ eqs c -> do
              flip enterClosure abstractToConcrete_ =<< reify . PConstr s ub =<< buildClosure c
          _ -> do
            cl <- reify $ PConstr s ub c
            enterClosure cl abstractToConcrete_

-- Copied from Agda.TypeChecking.Pretty.Warning.prettyConstraints
stripConstraintPids :: Constraints -> Constraints
stripConstraintPids cs = List.sortBy (compare `on` isBlocked) $ map stripPids cs
  where
    isBlocked = not . null . allBlockingProblems . constraintUnblocker
    interestingPids = Set.unions $ map (allBlockingProblems . constraintUnblocker) cs
    stripPids (PConstr pids unblock c) = PConstr (Set.intersection pids interestingPids) unblock c

-- | Converts an 'InteractionId' to a 'MetaId'.

interactionIdToMetaId :: ReadTCState m => InteractionId -> m MetaId
interactionIdToMetaId i = do
  h <- currentModuleNameHash
  return MetaId
    { metaId     = fromIntegral i
    , metaModule = h
    }

getConstraints' :: (ProblemConstraint -> TCM ProblemConstraint) -> (ProblemConstraint -> Bool) -> TCM [OutputForm C.Expr C.Expr]
getConstraints' g f = liftTCM $ do
    cs <- stripConstraintPids . filter f <$> (mapM g =<< M.getAllConstraints)
    cs <- forM cs $ \c -> do
            cl <- reify c
            enterClosure cl abstractToConcrete_
    ss <- mapM toOutputForm =<< getSolvedInteractionPoints True AsIs -- get all
    return $ ss ++ cs
  where
    toOutputForm (ii, mi, e) = do
      mv <- getMetaInfo <$> lookupLocalMeta mi
      withMetaInfo mv $ do
        mi <- interactionIdToMetaId ii
        let m = QuestionMark emptyMetaInfo{ metaNumber = Just mi } ii
        abstractToConcrete_ $ OutputForm noRange [] alwaysUnblock $ Assign m e

-- | Reify the boundary of an interaction point as something that can be
-- shown to the user.
getIPBoundary :: Rewrite -> InteractionId -> TCM [IPFace' C.Expr]
getIPBoundary norm ii = withInteractionId ii $ do
  ip <- lookupInteractionPoint ii

  io <- primIOne
  iz <- primIZero

  lookupInteractionMeta ii >>= \case
    Just mi -> do
      mv <- lookupLocalMeta mi

      let t = jMetaType $ mvJudgement mv
      telv@(TelV tel a) <- telView t

      reportSDoc "tc.ip.boundary" 30 $ TP.vcat
        [ "reifying interaction point boundary"
        , "tel:       " TP.<+> prettyTCM tel
        , "meta:      " TP.<+> prettyTCM mi
        ]
      reportSDoc "tc.ip.boundary" 30 $ "boundary:  " TP.<+> pure (pretty (getBoundary (ipBoundary ip)))

      withInteractionId ii $ do
      -- The boundary is a map associating terms (lambda abstractions)
      -- to IntMap Bools. The meta solver will wrap each LHS in lambdas
      -- corresponding to the interaction point's context. Each key of
      -- the boundary has a subset of (the interval variables in) the
      -- interaction point's context as a keysSet.
      as <- getContextArgs
      let
        c = abstractToConcrete_ <=< reifyUnblocked <=< normalForm norm
        go (im, rhs) = do
          reportSDoc "tc.ip.boundary" 30 $ TP.vcat
            [ "reifying constraint for face" TP.<+> TP.pretty im
            ]
          reportSDoc "tc.ip.boundary" 30 $ "term " TP.<+> TP.prettyTCM rhs
          -- Since the RHS is a lambda we have to apply it to the
          -- context:
          rhs <- c (rhs `apply` as)

          -- Reify the IntMap Bool as a list of (i = i0) (j = i1) terms:
          eqns <- forM (IntMap.toList im) $ \(a, b) -> do
            a <- c (I.Var a [])
            (,) a <$> c (if b then io else iz)
          pure $ IPFace' eqns rhs
      traverse go $ MapS.toList (getBoundary (ipBoundary ip))
    Nothing -> pure []

typeAndFacesInMeta :: InteractionId -> Rewrite -> Expr -> TCM (Expr, [IPFace' C.Expr])
typeAndFacesInMeta ii norm expr = withInteractionId ii $ do
  (ex, ty) <- inferExpr expr
  ty <- normalForm norm ty
  ip <- lookupInteractionPoint ii

  io <- primIOne
  iz <- primIZero
  let
    go im = do
      let
        c = abstractToConcrete_ <=< reifyUnblocked <=< normalForm norm
        fa = IntMap.toList im
        face (i, m) = inplaceS i $ if m then io else iz
        sub = foldr (\f s -> composeS (face f) s) idS fa
      eqns <- forM fa $ \(a, b) -> do
        a <- c (I.Var a [])
        (,) a <$> c (if b then io else iz)
      fmap (IPFace' eqns) . c =<< simplify (applySubst sub ex)

  faces <- traverse go $ MapS.keys (getBoundary (ipBoundary ip))
  ty <- reifyUnblocked ty
  pure (ty, faces)

-- | Goals and Warnings

getGoals :: TCM Goals
getGoals = getGoals' AsIs Simplified
  -- visible metas (as-is)
  -- hidden metas (unsolved implicit arguments simplified)

getGoals'
  :: Rewrite    -- ^ Degree of normalization of goals.
  -> Rewrite    -- ^ Degree of normalization of hidden goals.
  -> TCM Goals
getGoals' normVisible normHidden = do
  visibleMetas <- typesOfVisibleMetas normVisible
  hiddenMetas <- typesOfHiddenMetas normHidden
  return (visibleMetas, hiddenMetas)

-- | Print open metas nicely.
showGoals :: Goals -> TCM String
showGoals (ims, hms) = do
  di <- forM ims $ \ i ->
    withInteractionId (outputFormId $ OutputForm noRange [] alwaysUnblock i) $
      prettyATop i
  dh <- mapM showA' hms
  return $ unlines $ map show di ++ dh
  where
    showA' :: OutputConstraint A.Expr NamedMeta -> TCM String
    showA' m = do
      let i = nmid $ namedMetaOf m
      r <- getMetaRange i
      d <- withMetaId i (prettyATop m)
      return $ show d ++ "  [ at " ++ prettyShow r ++ " ]"

getWarningsAndNonFatalErrors :: TCM WarningsAndNonFatalErrors
getWarningsAndNonFatalErrors = do
  mws <- getAllWarnings AllWarnings
  let notMetaWarnings = filter (not . isMetaTCWarning) mws
  return $ case notMetaWarnings of
    ws@(_:_) -> classifyWarnings ws
    _ -> emptyWarningsAndNonFatalErrors

-- | Collecting the context of the given meta-variable.
getResponseContext
  :: Rewrite      -- ^ Normalise?
  -> InteractionId
  -> TCM [ResponseContextEntry]
getResponseContext norm ii = contextOfMeta ii norm

-- | @getSolvedInteractionPoints True@ returns all solutions,
--   even if just solved by another, non-interaction meta.
--
--   @getSolvedInteractionPoints False@ only returns metas that
--   are solved by a non-meta.

getSolvedInteractionPoints :: Bool -> Rewrite -> TCM [(InteractionId, MetaId, Expr)]
getSolvedInteractionPoints all norm = concat <$> do
  mapM solution =<< getInteractionIdsAndMetas
  where
    solution (i, m) = do
      mv <- lookupLocalMeta m
      withMetaInfo (getMetaInfo mv) $ do
        args  <- getContextArgs
        scope <- getScope
        let sol v = do
              -- Andreas, 2014-02-17 exclude metas solved by metas
              v <- instantiate v
              let isMeta = case v of MetaV{} -> True; _ -> False
              if isMeta && not all then return [] else do
                e <- blankNotInScope =<< reify =<< normalForm norm v
                return [(i, m, ScopedExpr scope e)]
            unsol = return []
        case mvInstantiation mv of
          InstV{}                        -> sol (MetaV m $ map Apply args)
          Open{}                         -> unsol
          OpenInstance{}                 -> unsol
          BlockedConst{}                 -> unsol
          PostponedTypeCheckingProblem{} -> unsol

typeOfMetaMI :: Rewrite -> MetaId -> TCM (OutputConstraint Expr NamedMeta)
typeOfMetaMI norm mi =
     do mv <- lookupLocalMeta mi
        withMetaInfo (getMetaInfo mv) $
          rewriteJudg mv (mvJudgement mv)
   where
    rewriteJudg :: MetaVariable -> Judgement MetaId ->
                   TCM (OutputConstraint Expr NamedMeta)
    rewriteJudg mv (HasType i cmp t) = do
      ms <- getMetaNameSuggestion i
      -- Andreas, 2019-03-17, issue #3638:
      -- Need to put meta type into correct context _before_ normalizing,
      -- otherwise rewrite rules in parametrized modules will not fire.
      vs <- getContextArgs
      t <- t `piApplyM` permute (takeP (size vs) $ mvPermutation mv) vs
      t <- normalForm norm t
      let x = NamedMeta ms i
      reportSDoc "interactive.meta" 10 $ TP.vcat
        [ TP.text $ unwords ["permuting", show i, "with", show $ mvPermutation mv]
        , TP.nest 2 $ TP.vcat
          [ "len  =" TP.<+> TP.text (show $ length vs)
          , "args =" TP.<+> prettyTCM vs
          , "t    =" TP.<+> prettyTCM t
          , "x    =" TP.<+> TP.pretty x
          ]
        ]
      reportSDoc "interactive.meta.scope" 20 $ TP.text $ show $ getMetaScope mv
      -- Andreas, 2016-01-19, issue #1783: need piApplyM instead of just piApply
      OfType x <$> reifyUnblocked t
    rewriteJudg mv (IsSort i t) = do
      ms <- getMetaNameSuggestion i
      return $ JustSort $ NamedMeta ms i


typeOfMeta :: Rewrite -> InteractionId -> TCM (OutputConstraint Expr InteractionId)
typeOfMeta norm ii = typeOfMeta' norm . (ii,) =<< lookupInteractionId ii

typeOfMeta' :: Rewrite -> (InteractionId, MetaId) -> TCM (OutputConstraint Expr InteractionId)
typeOfMeta' norm (ii, mi) = fmap (\_ -> ii) <$> typeOfMetaMI norm mi

typesOfVisibleMetas :: Rewrite -> TCM [OutputConstraint Expr InteractionId]
typesOfVisibleMetas norm =
  liftTCM $ mapM (typeOfMeta' norm) =<< getInteractionIdsAndMetas

typesOfHiddenMetas :: Rewrite -> TCM [OutputConstraint Expr NamedMeta]
typesOfHiddenMetas norm = liftTCM $ do
  is    <- getInteractionMetas
  store <- MapS.filterWithKey (implicit is) <$> useR stOpenMetaStore
  mapM (typeOfMetaMI norm) $ MapS.keys store
  where
  implicit is x m | isJust (mvTwin m) = False
  implicit is x m =
    case mvInstantiation m of
      M.InstV{} -> __IMPOSSIBLE__
      M.Open    -> x `notElem` is
      M.OpenInstance -> x `notElem` is  -- OR: True !?
      M.BlockedConst{} -> False
      M.PostponedTypeCheckingProblem{} -> False

-- | Create type of application of new helper function that would solve the goal.
metaHelperType :: Rewrite -> InteractionId -> Range -> String -> TCM (OutputConstraint' Expr Expr)
metaHelperType norm ii rng s = case words s of
  []    -> failure
  f : _ -> withInteractionId ii $ do
    ensureName f
    A.Application h args <- A.appView . getBody . deepUnscope <$> parseExprIn ii rng ("let " ++ f ++ " = _ in " ++ s)
    inCxt   <- hasElem <$> getContextNames
    cxtArgs <- getContextArgs
    a0      <- (`piApply` cxtArgs) <$> (getMetaType =<< lookupInteractionId ii)

    -- Konstantin, 2022-10-23: We don't want to print section parameters in helper type.
    freeVars <- getCurrentModuleFreeVars
    contextForAbstracting <- drop freeVars . reverse <$> getContext
    let escapeAbstractedContext = escapeContext impossible (length contextForAbstracting)

    case mapM (isVar . namedArg) args >>= \ xs -> xs <$ guard (all inCxt xs) of

     -- Andreas, 2019-10-11
     -- If all arguments are variables, there is no need to abstract.
     -- We simply make exactly the given arguments visible and all other hidden.
     Just xs -> do
      let inXs = hasElem xs
      let hideButXs dom = setHiding (if inXs $ fst $ unDom dom then NotHidden else Hidden) dom
      let tel = telFromList . map (fmap (first nameToArgName) . hideButXs) $ contextForAbstracting
      OfType' h <$> do
        -- Andreas, 2019-10-11: I actually prefer pi-types over ->.
        localTC (\e -> e { envPrintDomainFreePi = True }) $ escapeAbstractedContext $
          reify $ telePiVisible tel a0

     -- If some arguments are not variables.
     Nothing -> do
      -- cleanupType relies on with arguments being named 'w',
      -- so we'd better rename any actual 'w's to avoid confusion.
      let tel = runIdentity . onNamesTel unW . telFromList' nameToArgName $ contextForAbstracting
      let a = runIdentity . onNames unW $ a0
      vtys <- mapM (\ a -> fmap (Arg (getArgInfo a) . fmap OtherType) $ inferExpr $ namedArg a) args
      -- Remember the arity of a
      TelV atel _ <- telView a
      let arity = size atel
          (delta1, delta2, _, a', vtys') = splitTelForWith tel a vtys
      a <- localTC (\e -> e { envPrintDomainFreePi = True, envPrintMetasBare = True }) $ escapeAbstractedContext $ do
        reify =<< cleanupType arity args =<< normalForm norm =<< fst <$> withFunctionType delta1 vtys' delta2 a' []
      reportSDoc "interaction.helper" 10 $ TP.vcat $
        let extractOtherType = \case { OtherType a -> a; _ -> __IMPOSSIBLE__ } in
        let (vs, as)   = unzipWith (fmap extractOtherType . unArg) vtys in
        let (vs', as') = unzipWith (fmap extractOtherType . unArg) vtys' in
        [ "generating helper function"
        , TP.nest 2 $ "tel    = " TP.<+> inTopContext (prettyTCM tel)
        , TP.nest 2 $ "a      = " TP.<+> prettyTCM a
        , TP.nest 2 $ "vs     = " TP.<+> prettyTCM vs
        , TP.nest 2 $ "as     = " TP.<+> prettyTCM as
        , TP.nest 2 $ "delta1 = " TP.<+> inTopContext (prettyTCM delta1)
        , TP.nest 2 $ "delta2 = " TP.<+> inTopContext (addContext delta1 $ prettyTCM delta2)
        , TP.nest 2 $ "a'     = " TP.<+> inTopContext (addContext delta1 $ addContext delta2 $ prettyTCM a')
        , TP.nest 2 $ "as'    = " TP.<+> inTopContext (addContext delta1 $ prettyTCM as')
        , TP.nest 2 $ "vs'    = " TP.<+> inTopContext (addContext delta1 $ prettyTCM vs')
        ]
      return $ OfType' h a
  where
    failure = typeError $ GenericError $ "Expected an argument of the form f e1 e2 .. en"
    ensureName f = do
      ce <- parseExpr rng f
      flip (caseMaybe $ isName ce) (\ _ -> return ()) $ do
         reportSLn "interaction.helper" 10 $ "ce = " ++ show ce
         failure
    isVar :: A.Expr -> Maybe A.Name
    isVar = \case
      A.Var x -> Just x
      _ -> Nothing
    cleanupType arity args t = do
      -- Get the arity of t
      TelV ttel _ <- telView t
      -- Compute the number of pi-types subject to stripping.
      let n = size ttel - arity
      -- It cannot be negative, otherwise we would have performed a
      -- negative number of with-abstractions.
      unless (n >= 0) __IMPOSSIBLE__
      return $ evalState (renameVars $ stripUnused n t) args

    getBody (A.Let _ _ e)      = e
    getBody _                  = __IMPOSSIBLE__

    -- Strip the non-dependent abstractions from the first n abstractions.
    stripUnused n (El s v) = El s $ strip n v
    strip 0 = id
    strip n = \case
      I.Pi a b -> case stripUnused (n-1) <$> b of
        b | absName b == "w"   -> I.Pi a b
        NoAbs _ b              -> unEl b
        Abs s b | 0 `freeIn` b -> I.Pi (hide a) (Abs s b)
                | otherwise    -> strengthen impossible (unEl b)
      v -> v  -- todo: handle if goal type is a Pi

    -- renameVars = onNames (stringToArgName <.> renameVar . argNameToString)
    renameVars = onNames renameVar

    -- onNames :: Applicative m => (ArgName -> m ArgName) -> I.Type -> m I.Type
    onNames :: Applicative m => (String -> m String) -> I.Type -> m I.Type
    onNames f (El s v) = El s <$> onNamesTm f v

    -- onNamesTel :: Applicative f => (ArgName -> f ArgName) -> I.Telescope -> f I.Telescope
    onNamesTel :: Applicative f => (String -> f String) -> I.Telescope -> f I.Telescope
    onNamesTel f I.EmptyTel = pure I.EmptyTel
    onNamesTel f (I.ExtendTel a b) = I.ExtendTel <$> traverse (onNames f) a <*> onNamesAbs f onNamesTel b

    onNamesTm f = \case
      I.Var x es   -> I.Var x <$> onNamesElims f es
      I.Def q es   -> I.Def q <$> onNamesElims f es
      I.Con c ci args -> I.Con c ci <$> onNamesArgs f args
      I.Lam i b    -> I.Lam i <$> onNamesAbs f onNamesTm b
      I.Pi a b     -> I.Pi <$> traverse (onNames f) a <*> onNamesAbs f onNames b
      I.DontCare v -> I.DontCare <$> onNamesTm f v
      v@I.Lit{}    -> pure v
      v@I.Sort{}   -> pure v
      v@I.Level{}  -> pure v
      v@I.MetaV{}  -> pure v
      v@I.Dummy{}  -> pure v
    onNamesElims f = traverse $ traverse $ onNamesTm f
    onNamesArgs f  = traverse $ traverse $ onNamesTm f
    onNamesAbs f   = onNamesAbs' f (stringToArgName <.> f . argNameToString)
    onNamesAbs' f f' nd (Abs   s x) = Abs   <$> f' s <*> nd f x
    onNamesAbs' f f' nd (NoAbs s x) = NoAbs <$> f' s <*> nd f x

    unW "w" = return ".w"
    unW s   = return s

    renameVar "w" = betterName
    renameVar s   = pure s

    betterName = do
      xs <- get
      case xs of
        []         -> __IMPOSSIBLE__
        arg : args -> do
          put args
          return $ if
            | Arg _ (Named _ (A.Var x)) <- arg -> prettyShow $ A.nameConcrete x
            | Just x <- bareNameOf arg         -> argNameToString x
            | otherwise                        -> "w"


-- | Gives a list of names and corresponding types.
--   This list includes not only the local variables in scope, but also the let-bindings.

contextOfMeta :: InteractionId -> Rewrite -> TCM [ResponseContextEntry]
contextOfMeta ii norm = withInteractionId ii $ do
  info <- getMetaInfo <$> (lookupLocalMeta =<< lookupInteractionId ii)
  withMetaInfo info $ do
    -- List of local variables.
    cxt <- getContext
    let localVars = zipWith raise [1..] cxt
    -- List of let-bindings.
    letVars <- Map.toAscList <$> asksTC envLetBindings
    -- Reify the types and filter out bindings without a name.
    (++) <$> forMaybeM (reverse localVars) mkVar
         <*> forMaybeM letVars mkLet

  where
    mkVar :: ContextEntry -> TCM (Maybe ResponseContextEntry)
    mkVar Dom{ domInfo = ai, unDom = (name, t) } = do
      if shouldHide ai name then return Nothing else Just <$> do
        let n = nameConcrete name
        x  <- abstractToConcrete_ name
        let s = C.isInScope x
        ty <- reifyUnblocked =<< normalForm norm t
        return $ ResponseContextEntry n x (Arg ai ty) Nothing s

    mkLet :: (Name, Open M.LetBinding) -> TCM (Maybe ResponseContextEntry)
    mkLet (name, lb) = do
      LetBinding _ tm !dom <- getOpen lb
      if shouldHide (domInfo dom) name then return Nothing else Just <$> do
        let n = nameConcrete name
        x  <- abstractToConcrete_ name
        let s = C.isInScope x
        ty <- reifyUnblocked =<< normalForm norm dom
              -- Remove let bindings from x and later, to avoid folding to x = x, or using bindings
              -- not introduced when x was defined.
        v  <- removeLetBindingsFrom name $ reifyUnblocked =<< normalForm norm tm
        return $ ResponseContextEntry n x ty (Just v) s

    shouldHide :: ArgInfo -> A.Name -> Bool
    shouldHide ai n = not (isInstance ai) && (isNoName n || nameIsRecordName n)

-- | Returns the type of the expression in the current environment
--   We wake up irrelevant variables just in case the user want to
--   invoke that command in an irrelevant context.
typeInCurrent :: Rewrite -> Expr -> TCM Expr
typeInCurrent norm e =
    do  (_,t) <- wakeIrrelevantVars $ inferExpr e
        v <- normalForm norm t
        reifyUnblocked v



typeInMeta :: InteractionId -> Rewrite -> Expr -> TCM Expr
typeInMeta ii norm e =
   do   m <- lookupInteractionId ii
        mi <- getMetaInfo <$> lookupLocalMeta m
        withMetaInfo mi $
            typeInCurrent norm e

-- | The intro tactic.
--
-- Returns the terms (as strings) that can be
-- used to refine the goal. Uses the coverage checker
-- to find out which constructors are possible.
--
introTactic :: Bool -> InteractionId -> TCM [String]
introTactic pmLambda ii = do
  mi <- lookupInteractionId ii
  mv <- lookupLocalMeta mi
  withMetaInfo (getMetaInfo mv) $ case mvJudgement mv of
    HasType _ _ t -> do
        t <- reduce =<< piApplyM t =<< getContextArgs
        -- Andreas, 2013-03-05 Issue 810: skip hidden domains in introduction
        -- of constructor.
        TelV tel' t <- telViewUpTo' (-1) notVisible t
        -- if we cannot introduce a constructor, we try a lambda
        let fallback = do
              cubical <- isJust . optCubical <$> pragmaOptions
              TelV tel _ <- (if cubical then telViewPath else telView) t
              reportSDoc "interaction.intro" 20 $ TP.sep
                [ "introTactic/fallback"
                , "tel' = " TP.<+> prettyTCM tel'
                , "tel  = " TP.<+> prettyTCM tel
                ]
              case (tel', tel) of
                (EmptyTel, EmptyTel) -> return []
                _ -> introFun (telToList tel' ++ telToList tel)

        case unEl t of
          I.Def d _ -> do
            def <- getConstInfo d
            case theDef def of
              Datatype{}    -> addContext tel' $ introData AmbiguousNothing t
              Record{ recNamedCon = name }
                | name      -> addContext tel' $ introData AmbiguousConProjs t
                | otherwise -> addContext tel' $ introRec d
              _ -> fallback
          _ -> fallback
     `catchError` \_ -> return []
    _ -> __IMPOSSIBLE__
  where
    conName :: [NamedArg SplitPattern] -> [I.ConHead]
    conName [p] = [ c | I.ConP c _ _ <- [namedArg p] ]
    conName _   = __IMPOSSIBLE__

    showUnambiguousConName amb v =
       render . pretty <$> runAbsToCon (lookupQName amb $ I.conName v)

    showTCM :: PrettyTCM a => a -> TCM String
    showTCM v = render <$> prettyTCM v

    introFun :: ListTel -> TCM [String]
    introFun tel = addContext tel' $ do
        reportSDoc "interaction.intro" 10 $ do "introFun" TP.<+> prettyTCM (telFromList tel)
        imp <- showImplicitArguments
        let okHiding0 h = imp || h == NotHidden
            -- if none of the vars were displayed, we would get a parse error
            -- thus, we switch to displaying all
            allHidden   = not (any okHiding0 hs)
            okHiding    = if allHidden then const True else okHiding0
        vars <- -- setShowImplicitArguments (imp || allHidden) $
                applyWhen allHidden withShowAllArguments $
                  mapM showTCM [ setHiding h $ defaultArg $ var i :: Arg Term
                               | (h, i) <- zip hs $ downFrom n
                               , okHiding h
                               ]
        if pmLambda
           then return [ unwords $ ["λ", "{"] ++ vars ++ ["→", "?", "}"] ]
           else return [ unwords $ ["λ"]      ++ vars ++ ["→", "?"] ]
      where
        n = size tel
        hs   = map getHiding tel
        tel' = telFromList [ fmap makeName b | b <- tel ]
        makeName ("_", t) = ("x", t)
        makeName (x, t)   = (x, t)

    introData :: AllowAmbiguousNames -> I.Type -> TCM [String]
    introData amb t = do
      let tel  = telFromList [defaultDom ("_", t)]
          pat  = [defaultArg $ unnamed $ debruijnNamedVar "c" 0]
      r <- splitLast CoInductive tel pat
      case r of
        Left err -> return []
        Right cov ->
           mapM (showUnambiguousConName amb) $ concatMap (conName . scPats) $ splitClauses cov

    introRec :: QName -> TCM [String]
    introRec d = do
      hfs <- getRecordFieldNames d
      fs <- ifM showImplicitArguments
            (return $ map unDom hfs)
            (return [ unDom a | a <- hfs, visible a ])
      let e = C.Rec noRange $ for fs $ \ f ->
            Left $ C.FieldAssignment f $ C.QuestionMark noRange Nothing
      return [ prettyShow e ]
      -- Andreas, 2019-02-25, remark:
      -- prettyShow is ok here since we are just printing something like
      -- record { f1 = ? ; ... ; fn = ?}
      -- which does not involve any qualified names, and the fi are C.Name.

-- | Runs the given computation as if in an anonymous goal at the end
--   of the top-level module.
--
--   Sets up current module, scope, and context.
atTopLevel :: TCM a -> TCM a
atTopLevel m = inConcreteMode $ do
  let err = typeError $ GenericError "The file has not been loaded yet."
  caseMaybeM (useTC stCurrentModule) err $ \(current, topCurrent) -> do
    caseMaybeM (getVisitedModule topCurrent) __IMPOSSIBLE__ $ \ mi -> do
      let scope = iInsideScope $ miInterface mi
      tel <- lookupSection current
      -- Get the names of the local variables from @scope@
      -- and put them into the context.
      --
      -- Andreas, 2017-04-24, issue #2552:
      --
      -- Delete the let-bound ones, since they are not represented
      -- in the module telescope.
      --
      -- This is a temporary fix until a better solution is available,
      -- e.g., when the module telescope represents let-bound variables.
      --
      -- Unfortunately, referring to let-bound variables
      -- from the top level module telescope will for now result in a not-in-scope error.
      let names :: [A.Name]
          names = map localVar $ filter ((LetBound /=) . localBindingSource)
                               $ map snd $ reverse $ scope ^. scopeLocals
      -- Andreas, 2016-12-31, issue #2371
      -- The following is an unnecessary complication, as shadowed locals
      -- are not in scope anyway (they are ambiguous).
      -- -- Replace the shadowed names by fresh names (such that they do not shadow imports)
      -- let mnames :: [Maybe A.Name]
      --     mnames = map (notShadowedLocal . snd) $ reverse $ scopeLocals scope
      -- names <- mapM (maybe freshNoName_ return) mnames
      let types :: [Dom I.Type]
          types = map (snd <$>) $ telToList tel
          gamma :: ListTel' A.Name
          gamma = fromMaybe __IMPOSSIBLE__ $
                    zipWith' (\ x dom -> (x,) <$> dom) names types
      reportSDoc "interaction.top" 20 $ TP.vcat
        [ "BasicOps.atTopLevel"
        , "  names = " TP.<+> TP.sep (map prettyA   names)
        , "  types = " TP.<+> TP.sep (map prettyTCM types)
        ]
      M.withCurrentModule current $
        withScope_ scope $
          addContext gamma $ do
            -- We're going inside the top-level module, so we have to set the
            -- checkpoint for it and all its submodules to the new checkpoint.
            cp <- viewTC eCurrentCheckpoint
            stModuleCheckpoints `modifyTCLens` fmap (const cp)
            m

-- | Parse a name.
parseName :: Range -> String -> TCM C.QName
parseName r s = do
  e <- parseExpr r s
  let failure = typeError $ GenericError $ "Not an identifier: " ++ show e ++ "."
  maybe failure return $ isQName e

-- | Check whether an expression is a (qualified) identifier.
isQName :: C.Expr -> Maybe C.QName
isQName = \case
  C.Ident x                    -> return x
  _ -> Nothing

isName :: C.Expr -> Maybe C.Name
isName = isQName >=> \case
  C.QName x -> return x
  _ -> Nothing

-- | Returns the contents of the given module or record.

moduleContents
  :: Rewrite
     -- ^ How should the types be presented?
  -> Range
     -- ^ The range of the next argument.
  -> String
     -- ^ The module name.
  -> TCM ([C.Name], I.Telescope, [(C.Name, I.Type)])
     -- ^ Module names,
     --   context extension needed to print types,
     --   names paired up with corresponding types.

moduleContents norm rng s = traceCall ModuleContents $ do
  if null (trim s) then getModuleContents norm Nothing else do
  e <- parseExpr rng s
  case isQName e of
    -- If the expression is not a single identifier, it is not a module name
    -- and treated as a record expression.
    Nothing -> getRecordContents norm e
    -- Otherwise, if it is not in scope as a module name, it is treated
    -- as a record name.
    Just x  -> do
      ms :: [AbstractModule] <- scopeLookup x <$> getScope
      if null ms then getRecordContents norm e else getModuleContents norm $ Just x

-- | Returns the contents of the given record identifier.

getRecordContents
  :: Rewrite  -- ^ Amount of normalization in types.
  -> C.Expr   -- ^ Expression presumably of record type.
  -> TCM ([C.Name], I.Telescope, [(C.Name, I.Type)])
              -- ^ Module names,
              --   context extension,
              --   names paired up with corresponding types.
getRecordContents norm ce = do
  e <- toAbstract ce
  (_, t) <- inferExpr e
  let notRecordType = typeError $ ShouldBeRecordType t
  (q, vs, defn) <- fromMaybeM notRecordType $ isRecordType t
  case defn of
    Record{ recFields = fs, recTel = rtel } -> do
      let xs   = map (nameConcrete . qnameName . unDom) fs
          tel  = apply rtel vs
          doms = flattenTel tel
      -- Andreas, 2019-04-10, issue #3687: use flattenTel
      -- to bring types into correct scope.
      reportSDoc "interaction.contents.record" 20 $ TP.vcat
        [ "getRecordContents"
        , "  cxt  = " TP.<+> (prettyTCM =<< getContextTelescope)
        , "  tel  = " TP.<+> prettyTCM tel
        , "  doms = " TP.<+> prettyTCM doms
        , "  doms'= " TP.<+> addContext tel (prettyTCM doms)
        ]
      ts <- mapM (normalForm norm . unDom) doms
      return ([], tel, zip xs ts)
    _ -> __IMPOSSIBLE__

-- | Returns the contents of the given module.

getModuleContents
  :: Rewrite
       -- ^ Amount of normalization in types.
  -> Maybe C.QName
       -- ^ Module name, @Nothing@ if top-level module.
  -> TCM ([C.Name], I.Telescope, [(C.Name, I.Type)])
       -- ^ Module names,
       --   context extension,
       --   names paired up with corresponding types.
getModuleContents norm mm = do
  modScope <- case mm of
    Nothing -> getCurrentScope
    Just m  -> getNamedScope . amodName =<< resolveModule m
  let modules :: ThingsInScope AbstractModule
      modules = exportedNamesInScope modScope
      names :: ThingsInScope AbstractName
      names = exportedNamesInScope modScope
      xns = [ (x,n) | (x, ns) <- Map.toList names, n <- ns ]
  types <- forMaybeM xns $ \(x, n) -> do
    getConstInfo' (anameName n) >>= \case
      Right d -> do
        t <- normalForm norm =<< (defType <$> instantiateDef d)
        return $ Just (x, t)
      Left{} -> return Nothing
  return (Map.keys modules, EmptyTel, types)


whyInScope :: FilePath -> String -> TCM WhyInScopeData
whyInScope cwd s = do
  x     <- parseName noRange s
  scope <- getScope
  return $ WhyInScopeData
    x
    cwd
    (lookup x $ map (first C.QName) $ scope ^. scopeLocals)
    (scopeLookup x scope)
    (scopeLookup x scope)
