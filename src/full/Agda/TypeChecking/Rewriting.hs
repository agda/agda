{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Rewriting with arbitrary rules.
--
--   The user specifies a relation symbol by the pragma
--   @
--       {-\# BUILTIN REWRITE rel \#-}
--   @
--   where @rel@ should be of type @Δ → (lhs rhs : A) → Set i@.
--
--   Then the user can add rewrite rules by the pragma
--   @
--       {-\# REWRITE q \#-}
--   @
--   where @q@ should be a closed term of type @Γ → rel us lhs rhs@.
--
--   We then intend to add a rewrite rule
--   @
--       Γ ⊢ lhs ↦ rhs : B
--   @
--   to the signature where @B = A[us/Δ]@.
--
--   To this end, we normalize @lhs@, which should be of the form
--   @
--       f ts
--   @
--   for a @'Def'@-symbol f (postulate, function, data, record, constructor).
--   Further, @FV(ts) = dom(Γ)@.
--   The rule @q :: Γ ⊢ f ts ↦ rhs : B@ is added to the signature
--   to the definition of @f@.
--
--   When reducing a term @Ψ ⊢ f vs@ is stuck, we try the rewrites for @f@,
--   by trying to unify @vs@ with @ts@.
--   This is for now done by substituting fresh metas Xs for the bound
--   variables in @ts@ and checking equality with @vs@
--   @
--       Ψ ⊢ (f ts)[Xs/Γ] = f vs : B[Xs/Γ]
--   @
--   If successful (no open metas/constraints), we replace @f vs@ by
--   @rhs[Xs/Γ]@ and continue reducing.

module Agda.TypeChecking.Rewriting where

import Prelude hiding (null)

import Control.Monad

import Data.Foldable (toList)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Interaction.Options

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.MetaVars

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Free
import Agda.TypeChecking.Conversion
import qualified Agda.TypeChecking.Positivity.Occurrence as Pos
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive ( getBuiltinName )
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rewriting.Confluence
import Agda.TypeChecking.Rewriting.NonLinMatch
import Agda.TypeChecking.Rewriting.NonLinPattern
import Agda.TypeChecking.Warnings

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size
import qualified Agda.Utils.SmallSet as SmallSet

import Agda.Utils.Impossible
import Agda.Utils.Either

requireOptionRewriting :: TCM ()
requireOptionRewriting =
  unlessM (optRewriting <$> pragmaOptions) $ typeError NeedOptionRewriting

-- | Check that the name given to the BUILTIN REWRITE is actually
--   a relation symbol.
--   I.e., its type should be of the form @Δ → (lhs : A) (rhs : B) → Set ℓ@.
--   Note: we do not care about hiding/non-hiding of lhs and rhs.
verifyBuiltinRewrite :: Term -> Type -> TCM ()
verifyBuiltinRewrite v t = do
  requireOptionRewriting
  let failure reason = typeError . GenericDocError =<< sep
       [ prettyTCM v <+> " does not have the right type for a rewriting relation"
       , reason
       ]
  caseMaybeM (relView t)
    (failure $ "because it should accept at least two arguments") $
    \ (RelView tel delta a b core) -> do
    unless (visible a && visible b) $ failure $ "because its two final arguments are not both visible."
    case unEl core of
      Sort{}   -> return ()
      Con{}    -> __IMPOSSIBLE__
      Level{}  -> __IMPOSSIBLE__
      Lam{}    -> __IMPOSSIBLE__
      Pi{}     -> __IMPOSSIBLE__
      _ -> failure $ "because its type does not end in a sort, but in "
             <+> do inTopContext $ addContext tel $ prettyTCM core

-- | Deconstructing a type into @Δ → t → t' → core@.
data RelView = RelView
  { relViewTel   :: Telescope  -- ^ The whole telescope @Δ, t, t'@.
  , relViewDelta :: ListTel    -- ^ @Δ@.
  , relViewType  :: Dom Type   -- ^ @t@.
  , relViewType' :: Dom Type   -- ^ @t'@.
  , relViewCore  :: Type       -- ^ @core@.
  }

-- | Deconstructing a type into @Δ → t → t' → core@.
--   Returns @Nothing@ if not enough argument types.
relView :: Type -> TCM (Maybe RelView)
relView t = do
  TelV tel core <- telView t
  let n                = size tel
      (delta, lastTwo) = splitAt (n - 2) $ telToList tel
  if size lastTwo < 2 then return Nothing else do
    let [a, b] = fmap snd <$> lastTwo
    return $ Just $ RelView tel delta a b core

-- | Check the given rewrite rules and add them to the signature.
addRewriteRules :: [QName] -> TCM ()
addRewriteRules qs = do

  -- Check the rewrite rules
  rews <- mapM checkRewriteRule qs

  -- Add rewrite rules to the signature
  forM_ rews $ \rew -> do
    let f = rewHead rew
        matchables = getMatchables rew
    reportSDoc "rewriting" 10 $
      "adding rule" <+> prettyTCM (rewName rew) <+>
      "to the definition of" <+> prettyTCM f
    reportSDoc "rewriting" 30 $ "matchable symbols: " <+> prettyTCM matchables
    modifySignature $ addRewriteRulesFor f [rew] matchables

  -- Run confluence check for the new rules
  -- (should be done after adding all rules, see #3795)
  whenJustM (optConfluenceCheck <$> pragmaOptions) $ \confChk -> do
    -- Warn if --cubical is enabled
    whenJustM (optCubical <$> pragmaOptions) $ \_ -> genericWarning
      "Confluence checking for --cubical is not yet supported, confluence checking might be incomplete"
    -- Global confluence checker requires rules to be sorted
    -- according to the generality of their lhs
    when (confChk == GlobalConfluenceCheck) $
      forM_ (nubOn id $ map rewHead rews) sortRulesOfSymbol
    checkConfluenceOfRules confChk rews
    reportSDoc "rewriting" 10 $
      "done checking confluence of rules" <+> prettyList_ (map (prettyTCM . rewName) rews)

-- Auxiliary function for checkRewriteRule.
-- | Get domain of rewrite relation.
rewriteRelationDom :: QName -> TCM (ListTel, Dom Type)
rewriteRelationDom rel = do
  -- We know that the type of rel is that of a relation.
  relV <- relView =<< do defType <$> getConstInfo rel
  let RelView _tel delta a _a' _core = fromMaybe __IMPOSSIBLE__ relV
  reportSDoc "rewriting" 30 $ do
    "rewrite relation at type " <+> do
      inTopContext $ prettyTCM (telFromList delta) <+> " |- " <+> do
        addContext delta $ prettyTCM a
  return (delta, a)

-- | Check the validity of @q : Γ → rel us lhs rhs@ as rewrite rule
--   @
--       Γ ⊢ lhs ↦ rhs : B
--   @
--   where @B = A[us/Δ]@.
--   Remember that @rel : Δ → A → A → Set i@, so
--   @rel us : (lhs rhs : A[us/Δ]) → Set i@.
--   Returns the checked rewrite rule to be added to the signature.
checkRewriteRule :: QName -> TCM RewriteRule
checkRewriteRule q = do
  requireOptionRewriting
  let failNoBuiltin = typeError $ GenericError $
        "Cannot add rewrite rule without prior BUILTIN REWRITE"
  rels <- fromMaybeM failNoBuiltin getBuiltinRewriteRelations
  reportSDoc "rewriting.relations" 40 $ vcat
    [ "Rewrite relations:"
    , prettyList $ map prettyTCM $ toList rels
    ]
  def <- instantiateDef =<< getConstInfo q
  -- Issue 1651: Check that we are not adding a rewrite rule
  -- for a type signature whose body has not been type-checked yet.
  when (isEmptyFunction $ theDef def) $
    typeError . GenericDocError =<< hsep
      [ "Rewrite rule from function "
      , prettyTCM q
      , " cannot be added before the function definition"
      ]
  -- Get rewrite rule (type of q).
  TelV gamma1 core <- telView $ defType def
  reportSDoc "rewriting" 30 $ vcat
    [ "attempting to add rewrite rule of type "
    , prettyTCM gamma1
    , " |- " <+> do addContext gamma1 $ prettyTCM core
    ]
  let failureWrongTarget :: TCM a
      failureWrongTarget = typeError . GenericDocError =<< hsep
        [ prettyTCM q , " does not target rewrite relation" ]
  let failureBlocked :: Blocker -> TCM a
      failureBlocked b
        | not (null ms) = err $ "it contains the unsolved meta variable(s)" <+> prettyList_ (map prettyTCM $ Set.toList ms)
        | not (null ps) = err $ "it is blocked on problem(s)" <+> prettyList_ (map prettyTCM $ Set.toList ps)
        | not (null qs) = err $ "it requires the definition(s) of" <+> prettyList_ (map prettyTCM $ Set.toList qs)
        | otherwise = __IMPOSSIBLE__
        where
          err reason = typeError . GenericDocError =<< hsep
            [ prettyTCM q , " is not a legal rewrite rule, since" , reason ]
          ms = allBlockingMetas b
          ps = allBlockingProblems b
          qs = allBlockingDefs b
  let failureNotDefOrCon :: TCM a
      failureNotDefOrCon = typeError . GenericDocError =<< hsep
        [ prettyTCM q , " is not a legal rewrite rule, since the left-hand side is neither a defined symbol nor a constructor" ]
  let failureFreeVars :: IntSet -> TCM a
      failureFreeVars xs = typeError . GenericDocError =<< hsep
        [ prettyTCM q , " is not a legal rewrite rule, since the following variables are not bound by the left hand side: " , prettyList_ (map (prettyTCM . var) $ IntSet.toList xs) ]
  let failureNonLinearPars :: IntSet -> TCM a
      failureNonLinearPars xs = typeError . GenericDocError =<< do
        (prettyTCM q
          <+> " is not a legal rewrite rule, since the following parameters are bound more than once on the left hand side: "
          <+> hsep (List.intersperse "," $ map (prettyTCM . var) $ IntSet.toList xs))
          <> ". Perhaps you can use a postulate instead of a constructor as the head symbol?"
  let failureIllegalRule :: TCM a -- TODO:: Defined but not used
      failureIllegalRule = typeError . GenericDocError =<< hsep
        [ prettyTCM q , " is not a legal rewrite rule" ]

  -- Check that type of q targets rel.
  case unEl core of
    Def rel es@(_:_:_) | rel `elem` rels -> do
      (delta, a) <- rewriteRelationDom rel
      -- Because of the type of rel (Γ → sort), all es are applications.
      let vs = map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      -- The last two arguments are lhs and rhs.
          n  = size vs
          (us, [lhs, rhs]) = splitAt (n - 2) vs
      unless (size delta == size us) __IMPOSSIBLE__
      lhs <- instantiateFull lhs
      rhs <- instantiateFull rhs
      b   <- instantiateFull $ applySubst (parallelS $ reverse us) a

      gamma0 <- getContextTelescope
      gamma1 <- instantiateFull gamma1
      let gamma = gamma0 `abstract` gamma1

      -- 2017-06-18, Jesper: Unfold inlined definitions on the LHS.
      -- This is necessary to replace copies created by imports by their
      -- original definition.
      lhs <- modifyAllowedReductions (const $ SmallSet.singleton InlineReductions) $ reduce lhs

      -- Find head symbol f of the lhs, its type, its parameters (in case of a constructor), and its arguments.
      (f , hd , t , pars , es) <- case lhs of
        Def f es -> do
          def <- getConstInfo f
          checkAxFunOrCon f def
          return (f , Def f , defType def , [] , es)
        Con c ci vs -> do
          let hd = Con c ci
          ~(Just ((_ , _ , pars) , t)) <- getFullyAppliedConType c $ unDom b
          pars <- addContext gamma1 $ checkParametersAreGeneral c pars
          return (conName c , hd , t , pars , vs)
        _        -> failureNotDefOrCon

      ifNotAlreadyAdded f $ do

      addContext gamma1 $ do

        checkNoLhsReduction f hd es

        ps <- catchPatternErr failureBlocked $
          patternFrom Relevant 0 (t , Def f) es

        reportSDoc "rewriting" 30 $
          "Pattern generated from lhs: " <+> prettyTCM (PDef f ps)

        -- We need to check two properties on the variables used in the rewrite rule
        -- 1. For actually being able to apply the rewrite rule, we need
        --    that all variables that occur in the rule (on the left or the right)
        --    are bound in a pattern position on the left.
        -- 2. To preserve soundness, we need that all the variables that are used
        --    in the *proof* of the rewrite rule are bound in the lhs.
        --    For rewrite rules on constructors, we consider parameters to be bound
        --    even though they don't appear in the lhs, since they can be reconstructed.
        --    For postulated or abstract rewrite rules, we consider all arguments
        --    as 'used' (see #5238).
        let boundVars = nlPatVars ps
            freeVars  = allFreeVars (ps,rhs)
            allVars   = IntSet.fromList $ downFrom $ size gamma
            usedVars  = case theDef def of
              Function{}     -> usedArgs def
              Axiom{}        -> allVars
              AbstractDefn{} -> allVars
              _              -> __IMPOSSIBLE__
        reportSDoc "rewriting" 70 $
          "variables bound by the pattern: " <+> text (show boundVars)
        reportSDoc "rewriting" 70 $
          "variables free in the rewrite rule: " <+> text (show freeVars)
        reportSDoc "rewriting" 70 $
          "variables used by the rewrite rule: " <+> text (show usedVars)
        unlessNull (freeVars IntSet.\\ boundVars) failureFreeVars
        unlessNull (usedVars IntSet.\\ (boundVars `IntSet.union` IntSet.fromList pars)) failureFreeVars

        reportSDoc "rewriting" 70 $
          "variables bound in (erased) parameter position: " <+> text (show pars)
        unlessNull (boundVars `IntSet.intersection` IntSet.fromList pars) failureNonLinearPars

        let rew = RewriteRule q gamma f ps rhs (unDom b) False

        reportSDoc "rewriting" 10 $ vcat
          [ "checked rewrite rule" , prettyTCM rew ]
        reportSDoc "rewriting" 90 $ vcat
          [ "checked rewrite rule" , text (show rew) ]

        return rew

    _ -> failureWrongTarget

  where
    checkNoLhsReduction :: QName -> (Elims -> Term)  -> Elims -> TCM ()
    checkNoLhsReduction f hd es = do
      -- Skip this check when global confluence check is enabled, as
      -- redundant rewrite rules may be required to prove confluence.
      unlessM ((== Just GlobalConfluenceCheck) . optConfluenceCheck <$> pragmaOptions) $ do
      let v = hd es
      v' <- reduce v
      let fail :: TCM a
          fail = do
            reportSDoc "rewriting" 20 $ "v  = " <+> text (show v)
            reportSDoc "rewriting" 20 $ "v' = " <+> text (show v')
            typeError . GenericDocError =<< fsep
              [ prettyTCM q <+> " is not a legal rewrite rule, since the left-hand side "
              , prettyTCM v <+> " reduces to " <+> prettyTCM v' ]
      es' <- case v' of
        Def f' es'   | f == f'         -> return es'
        Con c' _ es' | f == conName c' -> return es'
        _                              -> fail
      unless (null es && null es') $ do
        a   <- computeElimHeadType f es es'
        pol <- getPolarity' CmpEq f
        ok  <- dontAssignMetas $ tryConversion $
                 compareElims pol [] a (Def f []) es es'
        unless ok fail

    checkAxFunOrCon :: QName -> Definition -> TCM ()
    checkAxFunOrCon f def = case theDef def of
      Axiom{}        -> return ()
      def@Function{} -> whenJust (maybeRight (funProjection def)) $ \proj ->
        case projProper proj of
          Just{} -> typeError . GenericDocError =<< hsep
            [ prettyTCM q , " is not a legal rewrite rule, since the head symbol"
            , prettyTCM f , "is a projection"
            ]
          Nothing -> typeError . GenericDocError =<< hsep
            [ prettyTCM q , " is not a legal rewrite rule, since the head symbol"
            , hd , "is a projection-like function."
            , "You can turn off the projection-like optimization for", hd
            , "with the pragma {-# NOT_PROJECTION_LIKE", hd, "#-}"
            , "or globally with the flag --no-projection-like"
            ]
            where hd = prettyTCM f
      Constructor{}  -> return ()
      AbstractDefn{} -> return ()
      Primitive{}    -> return () -- TODO: is this fine?
      _              -> typeError . GenericDocError =<< hsep
        [ prettyTCM q , " is not a legal rewrite rule, since the head symbol"
        , prettyTCM f , "is not a postulate, a function, or a constructor"
        ]

    ifNotAlreadyAdded :: QName -> TCM RewriteRule -> TCM RewriteRule
    ifNotAlreadyAdded f cont = do
      rews <- getRewriteRulesFor f
      -- check if q is already an added rewrite rule
      case List.find ((q ==) . rewName) rews of
        Just rew -> do
          genericWarning =<< do
            "Rewrite rule " <+> prettyTCM q <+> " has already been added"
          return rew
        Nothing -> cont

    usedArgs :: Definition -> IntSet
    usedArgs def = IntSet.fromList $ map snd $ usedIxs
      where
        occs = defArgOccurrences def
        allIxs = zip occs $ downFrom $ size occs
        usedIxs = filter (used . fst) allIxs
        used Pos.Unused = False
        used _          = True

    checkParametersAreGeneral :: ConHead -> Args -> TCM [Int]
    checkParametersAreGeneral c vs = do
        is <- loop vs
        unless (fastDistinct is) $ errorNotGeneral
        return is
      where
        loop []       = return []
        loop (v : vs) = case unArg v of
          Var i [] -> (i :) <$> loop vs
          _        -> errorNotGeneral

        errorNotGeneral :: TCM a
        errorNotGeneral = typeError . GenericDocError =<< vcat
            [ prettyTCM q <+> text " is not a legal rewrite rule, since the constructor parameters are not fully general:"
            , nest 2 $ text "Constructor: " <+> prettyTCM c
            , nest 2 $ text "Parameters: " <+> prettyList (map prettyTCM vs)
            ]

-- | @rewriteWith t f es rew@ where @f : t@
--   tries to rewrite @f es@ with @rew@, returning the reduct if successful.
rewriteWith :: Type
            -> (Elims -> Term)
            -> RewriteRule
            -> Elims
            -> ReduceM (Either (Blocked Term) Term)
rewriteWith t hd rew@(RewriteRule q gamma _ ps rhs b isClause) es
 | isClause = return $ Left $ NotBlocked ReallyNotBlocked $ hd es
 | otherwise = do
  traceSDoc "rewriting.rewrite" 50 (sep
    [ "{ attempting to rewrite term " <+> prettyTCM (hd es)
    , " having head " <+> prettyTCM (hd []) <+> " of type " <+> prettyTCM t
    , " with rule " <+> prettyTCM rew
    ]) $ do
  traceSDoc "rewriting.rewrite" 90 (sep
    [ "raw: attempting to rewrite term " <+> (text . show) (hd es)
    , " having head " <+> (text . show) (hd []) <+> " of type " <+> (text . show) t
    , " with rule " <+> (text . show) rew
    ]) $ do
  result <- nonLinMatch gamma (t,hd) ps es
  case result of
    Left block -> traceSDoc "rewriting.rewrite" 50 "}" $
      return $ Left $ block $> hd es -- TODO: remember reductions
    Right sub  -> do
      let v' = applySubst sub rhs
      traceSDoc "rewriting.rewrite" 50 (sep
        [ "rewrote " <+> prettyTCM (hd es)
        , " to " <+> prettyTCM v' <+> "}"
        ]) $ do
      return $ Right v'

-- | @rewrite b v rules es@ tries to rewrite @v@ applied to @es@ with the
--   rewrite rules @rules@. @b@ is the default blocking tag.
rewrite :: Blocked_ -> (Elims -> Term) -> RewriteRules -> Elims -> ReduceM (Reduced (Blocked Term) Term)
rewrite block hd rules es = do
  rewritingAllowed <- optRewriting <$> pragmaOptions
  if (rewritingAllowed && not (null rules)) then do
    (_ , t) <- fromMaybe __IMPOSSIBLE__ <$> getTypedHead (hd [])
    loop block t rules =<< instantiateFull' es -- TODO: remove instantiateFull?
  else
    return $ NoReduction (block $> hd es)
  where
    loop :: Blocked_ -> Type -> RewriteRules -> Elims -> ReduceM (Reduced (Blocked Term) Term)
    loop block t [] es =
      traceSDoc "rewriting.rewrite" 20 (sep
        [ "failed to rewrite " <+> prettyTCM (hd es)
        , "blocking tag" <+> text (show block)
        ]) $ do
      return $ NoReduction $ block $> hd es
    loop block t (rew:rews) es
     | let n = rewArity rew, length es >= n = do
          let (es1, es2) = List.genericSplitAt n es
          result <- rewriteWith t hd rew es1
          case result of
            Left (Blocked m u)    -> loop (block `mappend` Blocked m ()) t rews es
            Left (NotBlocked _ _) -> loop block t rews es
            Right w               -> return $ YesReduction YesSimplification $ w `applyE` es2
     | otherwise = loop (block `mappend` NotBlocked Underapplied ()) t rews es

    rewArity :: RewriteRule -> Int
    rewArity = length . rewPats
