{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}

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
import Control.Monad.Reader (local)

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
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rewriting.NonLinMatch
import qualified Agda.TypeChecking.Reduce.Monad as Red

import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

requireOptionRewriting :: TCM ()
requireOptionRewriting =
  unlessM (optRewriting <$> pragmaOptions) $ typeError NeedOptionRewriting

-- | Check that the name given to the BUILTIN REWRITE is actually
--   a relation symbol.
--   I.e., its type should be of the form @Δ → (lhs rhs : A) → Set ℓ@.
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
    case ignoreSharing (unEl core) of
      Sort{} -> do
        -- Check that the types of the last two arguments are equal.
        unlessM (tryConversion $
                   inTopContext $ addContext tel $ escapeContext 1 $
                     equalType (raise 1 a) b) $
          failure $ text $ "because the types of the last two arguments are different"
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
  , relViewType  :: Type       -- ^ @t@.
  , relViewType' :: Type       -- ^ @t'@.
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
    let [a, b] = snd . unDom <$> lastTwo
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
  Def rel _ <- primRewrite
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
  Just (RelView _tel delta a _a' _core) <- relView =<< do
    defType <$> getConstInfo rel
  reportSDoc "rewriting" 30 $ do
    text "rewrite relation at type " <+> do
      inTopContext $ prettyTCM (telFromList delta) <+> text " |- " <+> do
        addContext delta $ prettyTCM a
  -- Get rewrite rule (type of q).
  TelV gamma core <- telView $ defType def
  reportSDoc "rewriting" 30 $ do
    text "attempting to add rewrite rule of type " <+> do
      prettyTCM gamma <+> text " |- " <+> do
        addContext gamma $ prettyTCM core
  ctx <- getContext
  reportSDoc "rewriting" 40 $ do
    text "current context: " <+> prettyTCM ctx
  let failureWrongTarget = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " does not target rewrite relation" ]
  let failureMetas       = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " is not a legal rewrite rule, since it contains unsolved meta variables" ]
  let failureNotDefOrCon = typeError . GenericDocError =<< hsep
        [ prettyTCM q , text " is not a legal rewrite rule, since the left-hand side is neither a defined symbol nor a constructor" ]
  let failureFreeVars xs = typeError . GenericDocError =<< do
       addContext gamma $ hsep $
        [ prettyTCM q , text " is not a legal rewrite rule, since the following variables are not bound by the left hand side: " , prettyList_ (map (prettyTCM . var) xs) ]
  let failureLhsReduction lhs = typeError . GenericDocError =<< do
       addContext gamma $ hsep $
        [ prettyTCM q , text " is not a legal rewrite rule, since the left-hand side " , prettyTCM lhs , text " has top-level reductions" ]
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
      gamma <- instantiateFull gamma

      -- Find head symbol f of the lhs.
      f <- case ignoreSharing lhs of
        Def f es -> return f
        Con c vs -> return $ conName c
        _        -> failureNotDefOrCon

      -- Normalize lhs: we do not want to match redexes.
      lhs <- normaliseArgs lhs
      unlessM (isNormal lhs) $ failureLhsReduction lhs

      -- Normalize rhs: might be more efficient.
      rhs <- etaContract =<< normalise rhs
      unless (null $ allMetas (telToList gamma, lhs, rhs, b)) failureMetas
      pat <- patternFrom (size gamma) 0 lhs
      let rew = RewriteRule q gamma pat rhs b
      reportSDoc "rewriting" 10 $
        text "considering rewrite rule " <+> prettyTCM rew
      reportSDoc "rewriting" 60 $
        text "considering rewrite rule" <+> text (show rew)

      -- Check that all variables of Γ are pattern variables in the lhs.
      unlessNull ([0 .. size gamma - 1] List.\\ IntSet.toList (nlPatVars pat)) failureFreeVars

      -- -- check that FV(rhs) ⊆ nlPatVars(lhs)
      -- unless (allVars (freeVars rhs) `IntSet.isSubsetOf` nlPatVars pat) $
      --   failureFreeVars

      -- NO LONGER WORKS:
      -- -- Check whether lhs can be rewritten with itself.
      -- -- Otherwise, there are unbound variables in either gamma or rhs.
      -- addContext gamma $
      --   unlessM (isJust <$> runReduceM (rewriteWith (Just b) lhs rew)) $
      --     failureFreeVars

      -- Add rewrite rule gamma ⊢ lhs ↦ rhs : b for f.
      rew <- makeOpen rew
      addRewriteRules f [rew]

    _ -> failureWrongTarget
  where
    normaliseArgs :: Term -> TCM Term
    normaliseArgs v = case ignoreSharing v of
      Def f es -> Def f <$> do etaContract =<< normalise es
      Con c vs -> Con c <$> do etaContract =<< normalise vs
      _ -> __IMPOSSIBLE__

    isNormal :: Term -> TCM Bool
    isNormal v = do
      v' <- normalise v
      return $ v == v'

-- | Append rewrite rules to a definition.
addRewriteRules :: QName -> RewriteRules -> TCM ()
addRewriteRules f rews = do
  reportSDoc "rewriting" 10 $ text "rewrite rule ok, adding it to the definition of " <+> prettyTCM f
  modifySignature $ addRewriteRulesFor f rews
  --rules <- getRewriteRulesFor f
  --reportSDoc "rewriting" 20 $ vcat
  --  [ text "rewrite rules for " <+> prettyTCM f <+> text ":"
  --  , vcat (map prettyTCM rules)
  --  ]

-- | @rewriteWith t v rew@
--   tries to rewrite @v : t@ with @rew@, returning the reduct if successful.
rewriteWith :: Maybe Type -> Term -> RewriteRule -> ReduceM (Either (Blocked Term) Term)
rewriteWith mt v rew@(RewriteRule q gamma lhs rhs b) = do
  Red.traceSDoc "rewriting" 95 (sep
    [ text "attempting to rewrite term " <+> prettyTCM v
    , text " with rule " <+> prettyTCM rew
    ]) $ do
    result <- nonLinMatch lhs v
    case result of
      Left block -> return $ Left $ const v <$> block
      Right sub  -> do
        let v' = applySubst sub rhs
        Red.traceSDoc "rewriting" 90 (sep
          [ text "rewrote " <+> prettyTCM v
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

-- | @rewrite t@ tries to rewrite a reduced term.
rewrite :: Blocked Term -> ReduceM (Either (Blocked Term) Term)
rewrite bv = ifNotM (optRewriting <$> pragmaOptions) (return $ Left bv) $ {- else -} do
  let v     = ignoreBlocking bv
  case ignoreSharing v of
    -- We only rewrite @Def@s and @Con@s.
    Def f es -> rew f (Def f) es
    Con c vs -> rew (conName c) hd (Apply <$> vs)
      where hd es = Con c $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
    _ -> return $ Left bv
  where
    -- Try all rewrite rules for f.
    rew :: QName -> (Elims -> Term) -> Elims -> ReduceM (Either (Blocked Term) Term)
    rew f hd es = do
      rules <- getRewriteRulesFor f
      case rules of
        [] -> return $ Left $ bv $> hd es
        _  -> do
          es <- instantiateFull' es
          loop (void bv) es rules
      where
      loop :: Blocked_ -> Elims -> RewriteRules -> ReduceM (Either (Blocked Term) Term)
      loop block es [] = return $ Left $ block $> hd es
      loop block es (rew:rews) = do
        mrew <- tryOpen rew
        case mrew of
          Just rew | let n = rewArity rew, length es >= n -> do
            let (es1, es2) = List.genericSplitAt n es
            result <- rewriteWith Nothing (hd es1) rew
            case result of
              Left (Blocked m u)    -> loop (block `mappend` Blocked m ()) es rews
              Left (NotBlocked _ _) -> loop block es rews
              Right w               -> return $ Right $ w `applyE` es2
          _ -> loop (block `mappend` NotBlocked Underapplied ()) es rews

------------------------------------------------------------------------
-- * Auxiliary functions
------------------------------------------------------------------------

class NLPatVars a where
  nlPatVars :: a -> IntSet

instance (Foldable f, NLPatVars a) => NLPatVars (f a) where
  nlPatVars = foldMap nlPatVars

instance NLPatVars NLPat where
  nlPatVars p =
    case p of
      PVar i    -> singleton i
      PDef _ es -> nlPatVars es
      PWild     -> empty
      PLam _ p' -> nlPatVars $ unAbs p'
      PPi a b   -> nlPatVars a `IntSet.union` nlPatVars (unAbs b)
      PBoundVar _ es -> nlPatVars es
      PTerm{}   -> empty

rewArity :: RewriteRule -> Int
rewArity rew = case rewLHS rew of
  PDef _f es -> length es
  _          -> __IMPOSSIBLE__
