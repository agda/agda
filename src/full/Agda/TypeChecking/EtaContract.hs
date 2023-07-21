{-# OPTIONS_GHC -Wunused-imports #-}

-- | Compute eta short normal forms.
module Agda.TypeChecking.EtaContract where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce.Monad () --instance only
import {-# SOURCE #-} Agda.TypeChecking.Records
import {-# SOURCE #-} Agda.TypeChecking.Datatypes

import Agda.Utils.Monad
import Agda.Utils.List (initLast)

import Agda.Utils.Impossible

-- TODO: move to Agda.Syntax.Internal.SomeThing
data BinAppView = App Term (Arg Term)
                | NoApp Term

binAppView :: Term -> BinAppView
binAppView t = case t of
  Var i xs   -> appE (Var i) xs
  Def c xs   -> appE (Def c) xs
  -- Andreas, 2013-09-17: do not eta-contract when body is (record) constructor
  -- like in \ x -> s , x!  (See interaction/DoNotEtaContractFunIntoRecord)
  -- (Cf. also issue 889 (fixed differently).)
  -- At least record constructors should be fully applied where possible!
  -- TODO: also for ordinary constructors (\ x -> suc x  vs.  suc)?
  Con c ci xs
    | IsData <- conDataRecord c
             -> appE (Con c ci) xs
    | otherwise
             -> noApp
  Lit _      -> noApp
  Level _    -> noApp   -- could be an application, but let's not eta contract levels
  Lam _ _    -> noApp
  Pi _ _     -> noApp
  Sort _     -> noApp
  MetaV _ _  -> noApp
  DontCare _ -> noApp
  Dummy{}    -> __IMPOSSIBLE__
  where
    noApp = NoApp t
    appE f es0 | Just (es, Apply v) <- initLast es0 = App (f es) v
    appE _ _ = noApp

-- | Contracts all eta-redexes it sees without reducing.
{-# SPECIALIZE etaContract :: TermLike a => a -> TCM a #-}
{-# SPECIALIZE etaContract :: TermLike a => a -> ReduceM a #-}
etaContract :: (MonadTCEnv m, HasConstInfo m, HasOptions m, TermLike a) => a -> m a
etaContract = traverseTermM etaOnce

{-# SPECIALIZE etaOnce :: Term -> TCM Term #-}
{-# SPECIALIZE etaOnce :: Term -> ReduceM Term #-}
etaOnce :: (MonadTCEnv m, HasConstInfo m, HasOptions m) => Term -> m Term
etaOnce = \case
  -- Andreas, 2012-11-18: this call to reportSDoc seems to cost me 2%
  -- performance on the std-lib
  -- reportSDoc "tc.eta" 70 $ "eta-contracting" <+> prettyTCM v
  Lam i (Abs x b) -> etaLam i x b  -- NoAbs can't be eta'd

  -- Andreas, 2012-12-18:  Abstract definitions could contain
  -- abstract records whose constructors are not in scope.
  -- To be able to eta-contract them, we ignore abstract.
  Con c ci es -> etaCon c ci es etaContractRecord

  v -> return v

-- | If record constructor, call eta-contraction function.
etaCon :: (MonadTCEnv m, HasConstInfo m, HasOptions m)
  => ConHead  -- ^ Constructor name @c@.
  -> ConInfo  -- ^ Constructor info @ci@.
  -> Elims     -- ^ Constructor arguments @args@.
  -> (QName -> ConHead -> ConInfo -> Args -> m Term)
              -- ^ Eta-contraction workhorse, gets also name of record type.
  -> m Term   -- ^ Returns @Con c ci args@ or its eta-contraction.
etaCon c ci es cont = ignoreAbstractMode $ do
  let fallback = return $ Con c ci es
  -- reportSDoc "tc.eta" 20 $ "eta-contracting record" <+> prettyTCM t
  r <- getConstructorData $ conName c -- fails in ConcreteMode if c is abstract
  ifNotM (isEtaRecord r) fallback $ {-else-} do
    -- reportSDoc "tc.eta" 20 $ "eta-contracting record" <+> prettyTCM t
    let Just args = allApplyElims es
    cont r c ci args

-- | Try to contract a lambda-abstraction @Lam i (Abs x b)@.
etaLam :: (MonadTCEnv m, HasConstInfo m, HasOptions m)
  => ArgInfo  -- ^ Info @i@ of the 'Lam'.
  -> ArgName  -- ^ Name @x@ of the abstraction.
  -> Term     -- ^ Body ('Term') @b@ of the 'Abs'.
  -> m Term   -- ^ @Lam i (Abs x b)@, eta-contracted if possible.
etaLam i x b = do
    let fallback = return $ Lam i $ Abs x b
    case binAppView b of
      App u (Arg info v) -> do
        tyty <- typeInType
        if isVar0 tyty v
        -- Andreas, 2017-02-20 issue #2464
        -- Contracting with any irrelevant argument breaks subject reduction.
        -- E.g. \ .x -> f .(subst P eq x)  can in general not be contracted to f.
        -- -- (isIrrelevant info || isVar0 tyty v)
             && sameHiding i info
             && sameModality i info
             && not (freeIn 0 u)
           then return $ strengthen impossible u
           else fallback
      _ -> fallback
  where
    isVar0 _ (Var 0 [])               = True
    -- Andreas, 2016-01-08 If --type-in-type, all levels are equal.
    -- Jesper, 2019-10-15 issue #3073
    -- Contracting level arguments is not sound unless the domain type
    -- is in fact @Level@, e.g. @\(A : Set) → F lzero@ should not be
    -- eta-contracted to @F@.
    -- isVar0 True Level{}               = True
    isVar0 tyty (Level (Max 0 [Plus 0 l])) = isVar0 tyty l
    isVar0 _ _ = False
