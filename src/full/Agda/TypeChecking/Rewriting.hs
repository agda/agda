{-# LANGUAGE CPP               #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Rewriting with arbitrary rules.
--
--   The user specifies a relation symbol by the pragma
--   @
--       {-# BUILTIN REWRITE rel #-}
--   @
--   where @rel@ should be of type @Δ → (lhs rhs : A) → Set i@.
--
--   Then the user can add rewrite rules by the pragma
--   @
--       {-# REWRITE q #-}
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

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Reader (local, asks)

import Data.Foldable ( Foldable, foldMap )
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Monoid

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Conversion
import qualified Agda.TypeChecking.Positivity.Occurrence as Pos
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive ( getBuiltinName )
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rewriting.NonLinMatch
import qualified Agda.TypeChecking.Reduce.Monad as Red

import Agda.Utils.Functor
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Lens
import qualified Agda.Utils.HashMap as HMap

#include "undefined.h"
import Agda.Utils.Impossible

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
       [ prettyTCM v <+> text " does not have the right type for a rewriting relation"
       , reason
       ]
  caseMaybeM (relView t)
    (failure $ text "because it should accept at least two arguments") $
    \ (RelView tel delta a b core) -> do
    unless (visible a && visible b) $ failure $ text "because its two final arguments are not both visible."
    case ignoreSharing (unEl core) of
      Sort{}   -> return ()
      Con{}    -> __IMPOSSIBLE__
      Level{}  -> __IMPOSSIBLE__
      Lam{}    -> __IMPOSSIBLE__
      Pi{}     -> __IMPOSSIBLE__
      Shared{} -> __IMPOSSIBLE__
      _ -> failure $ text "because its type does not end in a sort, but in "
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

-- | Add @q : Γ → rel us lhs rhs@ as rewrite rule
--   @
--       Γ ⊢ lhs ↦ rhs : B
--   @
--   to the signature where @B = A[us/Δ]@.
--   Remember that @rel : Δ → A → A → Set i@, so
--   @rel us : (lhs rhs : A[us/Δ]) → Set i@.
addRewriteRule :: QName -> TCM ()
addRewriteRule q = do
  requireOptionRewriting
  let failNoBuiltin = typeError $ GenericError $
        "Cannot add rewrite rule without prior BUILTIN REWRITE"
  rel <- fromMaybeM failNoBuiltin $ getBuiltinName builtinRewrite
  def <- instantiateDef =<< getConstInfo q
  -- Issue 1651: Check that we are not adding a rewrite rule
  -- for a type signature whose body has not been type-checked yet.
  when (isEmptyFunction $ theDef def) $
    typeError . GenericDocError =<< hsep
      [ text "Rewrite rule from function "
      , prettyTCM q
      , text " cannot be added before the function definition"
      ]
  -- We know that the type of rel is that of a relation.
  relV <- relView =<< do defType <$> getConstInfo rel
  let RelView _tel delta a _a' _core = -- line break for CPP
        fromMaybe __IMPOSSIBLE__ relV
  reportSDoc "rewriting" 30 $ do
    text "rewrite relation at type " <+> do
      inTopContext $ prettyTCM (telFromList delta) <+> text " |- " <+> do
        addContext delta $ prettyTCM a
  -- Get rewrite rule (type of q).
  TelV gamma1 core <- telView $ defType def
  reportSDoc "rewriting" 30 $ do
    text "attempting to add rewrite rule of type " <+> do
      prettyTCM gamma1 <+> text " |- " <+> do
        addContext gamma1 $ prettyTCM core
  let failureWrongTarget = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " does not target rewrite relation" ]
  let failureMetas       = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " is not a legal rewrite rule, since it contains unsolved meta variables" ]
  let failureNotDefOrCon = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " is not a legal rewrite rule, since the left-hand side is neither a defined symbol nor a constructor" ]
  let failureFreeVars xs = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " is not a legal rewrite rule, since the following variables are not bound by the left hand side: " , prettyList_ (map (prettyTCM . var) $ IntSet.toList xs) ]
  let failureIllegalRule = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " is not a legal rewrite rule" ]

  -- Check that type of q targets rel.
  case ignoreSharing $ unEl core of
    Def rel' es@(_:_:_) | rel == rel' -> do
      -- Because of the type of rel (Γ → sort), all es are applications.
      let vs = map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      -- The last two arguments are lhs and rhs.
          n  = size vs
          (us, [lhs, rhs]) = splitAt (n - 2) vs
      unless (size delta == size us) __IMPOSSIBLE__
      b <- instantiateFull $ applySubst (parallelS $ reverse us) a

      gamma0 <- getContextTelescope
      gamma1 <- instantiateFull gamma1
      let gamma = gamma0 `abstract` gamma1

      unless (null $ allMetas (telToList gamma1)) $ do
        reportSDoc "rewriting" 30 $ text "metas in gamma1: " <+> text (show $ allMetas $ telToList gamma1)
        failureMetas

      -- Find head symbol f of the lhs and its arguments.
      (f , hd , es) <- case ignoreSharing lhs of
        Def f es -> return (f , Def f , es)
        Con c ci vs -> do
          let hd = Con c ci . fromMaybe __IMPOSSIBLE__ . allApplyElims
          return (conName c , hd  , map Apply vs)
        _        -> failureNotDefOrCon

      rew <- addContext gamma1 $ do
        -- Normalize lhs args: we do not want to match redexes.
        es <- etaContract =<< normalise es
        checkNoLhsReduction f (hd es)

        -- Normalize rhs: might be more efficient.
        rhs <- etaContract =<< normalise rhs
        unless (null $ allMetas (es, rhs, b)) $ do
          reportSDoc "rewriting" 30 $ text "metas in lhs: " <+> text (show $ allMetas es)
          reportSDoc "rewriting" 30 $ text "metas in rhs: " <+> text (show $ allMetas rhs)
          reportSDoc "rewriting" 30 $ text "metas in b  : " <+> text (show $ allMetas b)
          failureMetas
        ps <- patternFrom Relevant 0 es
        reportSDoc "rewriting" 30 $
          text "Pattern generated from lhs: " <+> prettyTCM (PDef f ps)

        -- check that FV(rhs) ⊆ nlPatVars(lhs)
        let freeVars  = usedArgs (defArgOccurrences def) `IntSet.union` allFreeVars (ps,rhs)
            boundVars = nlPatVars ps
        reportSDoc "rewriting" 40 $
          text "variables bound by the pattern: " <+> text (show boundVars)
        reportSDoc "rewriting" 40 $
          text "variables free in the rewrite rule: " <+> text (show freeVars)
        unlessNull (freeVars IntSet.\\ boundVars) failureFreeVars

        return $ RewriteRule q gamma f ps rhs (unDom b)

      reportSDoc "rewriting" 10 $
        text "considering rewrite rule " <+> prettyTCM rew
      reportSDoc "rewriting" 60 $
        text "considering rewrite rule" <+> text (show rew)

      -- NO LONGER WORKS:
      -- -- Check whether lhs can be rewritten with itself.
      -- -- Otherwise, there are unbound variables in either gamma or rhs.
      -- addContext gamma $
      --   unlessM (isJust <$> runReduceM (rewriteWith (Just b) lhs rew)) $
      --     failureFreeVars

      -- Add rewrite rule gamma ⊢ lhs ↦ rhs : b for f.
      addRewriteRules f [rew]

    _ -> failureWrongTarget
  where
    checkNoLhsReduction :: QName -> Term -> TCM ()
    checkNoLhsReduction f v = do
      v' <- normalise v
      unless (v == v') $ do
        reportSDoc "rewriting" 20 $ text "v  = " <+> text (show v)
        reportSDoc "rewriting" 20 $ text "v' = " <+> text (show v')
        -- Andreas, 2016-06-01, issue 1997
        -- A reason for a reduction of the lhs could be that
        -- the rewrite rule has already been added.
        -- In this case, we want a nicer error message.
        checkNotAlreadyAdded f
        typeError . GenericDocError =<< fsep
          [ prettyTCM q <+> text " is not a legal rewrite rule, since the left-hand side "
          , prettyTCM v <+> text " reduces to " <+> prettyTCM v' ]

    checkNotAlreadyAdded :: QName -> TCM ()
    checkNotAlreadyAdded f = do
      rews <- getRewriteRulesFor f
      -- check if q is already an added rewrite rule
      when (any ((q ==) . rewName) rews) $
        typeError . GenericDocError =<< do
          text "Rewrite rule " <+> prettyTCM q <+> text " has already been added"

    usedArgs :: [Pos.Occurrence] -> IntSet
    usedArgs occs = IntSet.fromList $ map snd $ usedIxs
      where
        allIxs = zip occs $ downFrom $ size occs
        usedIxs = filter (used . fst) allIxs
        used Pos.Unused = False
        used _          = True

-- | Append rewrite rules to a definition.
addRewriteRules :: QName -> RewriteRules -> TCM ()
addRewriteRules f rews = do
  reportSDoc "rewriting" 10 $ text "rewrite rule ok, adding it to the definition of " <+> prettyTCM f
  let matchables = getMatchables rews
  reportSDoc "rewriting" 30 $ text "matchable symbols: " <+> prettyTCM matchables
  modifySignature $ addRewriteRulesFor f rews matchables
  --rules <- getRewriteRulesFor f
  --reportSDoc "rewriting" 20 $ vcat
  --  [ text "rewrite rules for " <+> prettyTCM f <+> text ":"
  --  , vcat (map prettyTCM rules)
  --  ]

-- | Sledgehammer approach to local rewrite rules. Rebind them after each
--   left-hand side (which scrambles the context).
rebindLocalRewriteRules :: TCM ()
rebindLocalRewriteRules = do
  current <- currentModule
  ruleMap <- use $ stSignature . sigRewriteRules
  let isLocal r = m == current || m `isSubModuleOf` current
        where m = qnameModule $ rewName r
      ruleMap' = HMap.map (filter (not . isLocal)) ruleMap
      locals = map rewName $ filter isLocal $ concat $ map reverse $ HMap.elems ruleMap
  unless (null locals) $ __CRASH_WHEN__ "rewriting.local.crash" 1000
  stSignature . sigRewriteRules .= ruleMap'
  mapM_ addRewriteRule locals

-- | @rewriteWith t f es rew@
--   tries to rewrite @f es : t@ with @rew@, returning the reduct if successful.
rewriteWith :: Maybe Type
            -> Term
            -> RewriteRule
            -> Elims
            -> ReduceM (Either (Blocked Term) Term)
rewriteWith mt v rew@(RewriteRule q gamma _ ps rhs b) es = do
  Red.traceSDoc "rewriting" 75 (sep
    [ text "attempting to rewrite term " <+> prettyTCM (v `applyE` es)
    , text " with rule " <+> prettyTCM rew
    ]) $ do
    result <- nonLinMatch gamma ps es
    case result of
      Left block -> return $ Left $ block $> v `applyE` es -- TODO: remember reductions
      Right sub  -> do
        let v' = applySubst sub rhs
        Red.traceSDoc "rewriting" 70 (sep
          [ text "rewrote " <+> prettyTCM (v `applyE` es)
          , text " to " <+> prettyTCM v'
          ]) $ return $ Right v'

    {- OLD CODE:
    -- Freeze all metas, remember which one where not frozen before.
    -- This ensures that we do not instantiate metas while matching
    -- on the rewrite lhs.
    ms <- freezeMetas
    res <- tryConversion' $ do

      -- Create new metas for the lhs variables of the rewriting rule.
      xs <- newTelMeta gamma
      let sigma        = parallelS $ map unArg xs
          (lhs', rhs', b') = applySubst sigma (lhs, rhs, b)
      -- Unify type and term with type and lhs of rewrite rule.
      whenJust mt $ \ t -> leqType t b'
      local (\ e -> e {envCompareBlocked = True}) $ equalTerm b' lhs' v
      -- Check that all variables have been solved for.
      unlessM (isInstantiatedMeta xs) $ do
        reportSDoc "rewriting" 20 $ text "lhs variables solved with: " <+> do
          sep $ map prettyTCM xs
        -- The following error is caught immediately by tryConversion.
        typeError $ GenericError $ "free variables not bound by left hand side"
      return rhs'

    -- Thaw metas that were frozen by a call to this function.
    unfreezeMetas' (`elem` ms)
    return res-}

-- | @rewrite b v rules es@ tries to rewrite @v@ applied to @es@ with the
--   rewrite rules @rules@. @b@ is the default blocking tag.
rewrite :: Blocked_ -> Term -> RewriteRules -> Elims -> ReduceM (Reduced (Blocked Term) Term)
rewrite block v rules es = do
  rewritingAllowed <- optRewriting <$> pragmaOptions
  if (rewritingAllowed && not (null rules)) then
    loop block rules =<< instantiateFull' es
  else
    return $ NoReduction (block $> v `applyE` es)
  where
    loop :: Blocked_ -> RewriteRules -> Elims -> ReduceM (Reduced (Blocked Term) Term)
    loop block [] es = return $ NoReduction $ block $> v `applyE` es
    loop block (rew:rews) es
     | let n = rewArity rew, length es >= n = do
          let (es1, es2) = List.genericSplitAt n es
          result <- rewriteWith Nothing v rew es1
          case result of
            Left (Blocked m u)    -> loop (block `mappend` Blocked m ()) rews es
            Left (NotBlocked _ _) -> loop block rews es
            Right w               -> return $ YesReduction YesSimplification $ w `applyE` es2
     | otherwise = loop (block `mappend` NotBlocked Underapplied ()) rews es


------------------------------------------------------------------------
-- * Auxiliary functions
------------------------------------------------------------------------

class NLPatVars a where
  nlPatVars :: a -> IntSet

instance (Foldable f, NLPatVars a) => NLPatVars (f a) where
  nlPatVars = foldMap nlPatVars

instance NLPatVars NLPType where
  nlPatVars (NLPType l a) = nlPatVars l `IntSet.union` nlPatVars a

instance NLPatVars NLPat where
  nlPatVars p =
    case p of
      PVar _ i _ -> singleton i
      PDef _ es -> nlPatVars es
      PWild     -> empty
      PLam _ p' -> nlPatVars $ unAbs p'
      PPi a b   -> nlPatVars a `IntSet.union` nlPatVars (unAbs b)
      PBoundVar _ es -> nlPatVars es
      PTerm{}   -> empty

rewArity :: RewriteRule -> Int
rewArity = length . rewPats

-- | Erase the CtxId's of rewrite rules
class KillCtxId a where
  killCtxId :: a -> a

instance (Functor f, KillCtxId a) => KillCtxId (f a) where
  killCtxId = fmap killCtxId

instance KillCtxId RewriteRule where
  killCtxId rule@RewriteRule{ rewPats = ps } = rule{ rewPats = killCtxId ps }

instance KillCtxId NLPType where
  killCtxId (NLPType l a) = NLPType (killCtxId l) (killCtxId a)

instance KillCtxId NLPat where
  killCtxId p = case p of
    PVar _ i bvs   -> PVar Nothing i bvs
    PWild          -> p
    PDef f es      -> PDef f $ killCtxId es
    PLam i x       -> PLam i $ killCtxId x
    PPi a b        -> PPi (killCtxId a) (killCtxId b)
    PBoundVar i es -> PBoundVar i $ killCtxId es
    PTerm _        -> p

-- | Get all symbols that a rewrite rule matches against
class GetMatchables a where
  getMatchables :: a -> [QName]

instance (Foldable f, GetMatchables a) => GetMatchables (f a) where
  getMatchables = foldMap getMatchables

instance GetMatchables NLPat where
  getMatchables p =
    case p of
      PVar _ _ _     -> empty
      PWild          -> empty
      PDef f _       -> singleton f
      PLam _ x       -> empty
      PPi a b        -> empty
      PBoundVar i es -> empty
      PTerm _        -> empty -- should be safe (I hope)

instance GetMatchables RewriteRule where
  getMatchables = getMatchables . rewPats

-- Only computes free variables that are not bound (i.e. those in a PTerm)
instance Free NLPat where
  freeVars' p = case p of
    PVar _ _ _ -> mempty
    PWild -> mempty
    PDef _ es -> freeVars' es
    PLam _ u -> freeVars' u
    PPi a b -> freeVars' (a,b)
    PBoundVar _ es -> freeVars' es
    PTerm t -> freeVars' t

instance Free NLPType where
  freeVars' (NLPType l a) =
    ifM ((IgnoreNot ==) <$> asks feIgnoreSorts)
      {- then -} (freeVars' (l, a))
      {- else -} (freeVars' a)
