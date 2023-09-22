{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.IApplyConfluence where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Monad.Except

import Data.Bifunctor (first, second)
import Data.DList (DList)
import Data.Foldable (toList)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.Interaction.Options

import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope.Path
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute

import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Maybe
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Impossible
import Agda.Utils.Functor


checkIApplyConfluence_ :: QName -> TCM ()
checkIApplyConfluence_ f = whenM (isJust . optCubical <$> pragmaOptions) $ do
  -- Andreas, 2019-03-27, iapply confluence should only be checked
  -- when --cubical or --erased-cubical is active. See
  -- test/Succeed/CheckIApplyConfluence.agda.
  -- We cannot reach the following crash point unless
  -- --cubical/--erased-cubical is active.
  __CRASH_WHEN__ "tc.cover.iapply.confluence.crash" 666
  reportSDoc "tc.cover.iapply" 10 $ text "Checking IApply confluence of" <+> pretty f
  inConcreteOrAbstractMode f $ \ d -> do
  case theDef d of
    Function{funClauses = cls', funCovering = cls} -> do
      reportSDoc "tc.cover.iapply" 10 $ text "length cls =" <+> pretty (length cls)
      when (null cls && any (not . null . iApplyVars . namedClausePats) cls') $
        __IMPOSSIBLE__
      unlessM (optKeepCoveringClauses <$> pragmaOptions) $
        modifySignature $ updateDefinition f $ updateTheDef
          $ updateCovering (const [])

      traceCall (CheckFunDefCall (getRange f) f [] False) $
        forM_ cls $ checkIApplyConfluence f
    _ -> return ()

-- | @checkIApplyConfluence f (Clause {namedClausePats = ps})@ checks that @f ps@
-- reduces in a way that agrees with @IApply@ reductions.
checkIApplyConfluence :: QName -> Clause -> TCM ()
checkIApplyConfluence f cl = case cl of
      Clause {clauseBody = Nothing} -> return ()
      Clause {clauseType = Nothing} -> __IMPOSSIBLE__
      -- Inserted clause, will respect boundaries whenever the
      -- user-written clauses do. Saves a ton of work!
      Clause {namedClausePats = ps} | hasDefP ps -> pure ()
      cl@Clause { clauseTel = clTel
                , namedClausePats = ps
                , clauseType = Just t
                , clauseBody = Just body
                } -> setCurrentRange (clauseLHSRange cl) $ do
          let
            trhs = unArg t
          oldCall <- asksTC envCall
          reportSDoc "tc.cover.iapply" 40 $ "tel =" <+> prettyTCM clTel
          reportSDoc "tc.cover.iapply" 40 $ "ps =" <+> pretty ps
          ps <- normaliseProjP ps
          forM_ (iApplyVars ps) $ \ i -> do
            unview <- intervalUnview'
            let phi = unview $ IMax (argN $ unview (INeg $ argN $ var i)) $ argN $ var i
            let es = patternsToElims ps
            let lhs = Def f es

            reportSDoc "tc.cover.iapply" 40 $ text "clause:" <+> pretty ps <+> "->" <+> pretty body
            reportSDoc "tc.cover.iapply" 20 $ "body =" <+> prettyTCM body
            inTopContext $ reportSDoc "tc.cover.iapply" 20 $ "Γ =" <+> prettyTCM clTel

            let
              k :: Substitution -> Comparison -> Type -> Term -> Term -> TCM ()
              -- TODO (Amy, 2023-07-08): Simplifying the LHS of a
              -- generated clause in its context is loopy, see #6722
              k phi cmp ty u v | hasDefP ps = compareTerm cmp ty u v
              k phi cmp ty u v = do
                u_e   <- simplify u
                -- Issue #6725: Print these terms in their own TC state.
                -- If printing the values before entering the conversion
                -- checker is too expensive then we could save the TC
                -- state and print them when erroring instead, but that
                -- might cause space leaks.
                (u_p, v_p) <- (,) <$> prettyTCM u_e <*> (prettyTCM =<< simplify v)

                let
                  -- Make note of the context (literally): we're
                  -- checking that this specific clause in f is
                  -- confluent with IApply reductions. That way if we
                  -- can tell the user what the endpoints are.
                  why = CheckIApplyConfluence
                    (getRange cl) f
                    (applySubst phi lhs)
                    u_e v ty

                  -- But if the conversion checking failed really early, we drop the extra
                  -- information. In that case, it's just noise.
                  maybeDropCall e@(TypeError loc s err)
                    | UnequalTerms _ u' v' _ <- clValue err =
                      -- Issue #6725: restore the TC state from the
                      -- error before dealing with the stored terms.
                      withTCState (const s) $ enterClosure err $ \e' -> do
                        u' <- prettyTCM =<< simplify u'
                        v' <- prettyTCM =<< simplify v'

                        -- Specifically, we compare how the things are pretty-printed, to avoid
                        -- double-printing, rather than a more refined heuristic, since the
                        -- “failure case” here is *at worst* accidentally reminding the user of how
                        -- IApplyConfluence works.
                        if (u_p == u' && v_p == v')
                          then localTC (\e -> e { envCall = oldCall }) $ typeError e'
                          else throwError e
                  maybeDropCall x = throwError x

                -- Note: Any postponed constraint with this call *will* have the extra
                -- information. This is a feature: if the constraint is woken up later,
                -- then it's probably a good idea to remind the user of what's going on,
                -- instead of presenting a mysterious error.
                traceCall why (compareTerm cmp ty u v `catchError` maybeDropCall)

            addContext clTel $ compareTermOnFace' k CmpEq phi trhs lhs body

-- | current context is of the form Γ.Δ
unifyElims :: Args
              -- ^ variables to keep   Γ ⊢ x_n .. x_0 : Γ
           -> Args
              -- ^ variables to solve  Γ.Δ ⊢ ts : Γ
           -> (Substitution -> [(Term,Term)] -> TCM a)
              -- Γ.Δ' ⊢ σ : Γ.Δ
              -- Γ.Δ' new current context.
              -- Γ.Δ' ⊢ [(x = u)]
              -- Γ.Δ', [(x = u)] ⊢ id_g = ts[σ] : Γ
           -> TCM a
unifyElims vs ts k = do
  dom <- getContext
  let (binds' , eqs' ) = candidate (map unArg vs) (map unArg ts)
      (binds'', eqss') =
        unzip $
        map (\(j, tts) -> case toList tts of
                t : ts -> ((j, t), map (, var j) ts)
                []     -> __IMPOSSIBLE__) $
        IntMap.toList $ IntMap.fromListWith (<>) binds'
      cod'  = codomain s (IntSet.fromList $ map fst binds'')
      cod   = cod' dom
      svs   = size vs
      binds = IntMap.fromList $
              map (second (raise (size cod - svs))) binds''
      eqs   = map (first  (raise (size dom - svs))) $
              eqs' ++ concat eqss'
      s     = bindS binds
  updateContext s cod' $ k s (s `applySubst` eqs)
  where
  candidate :: [Term] -> [Term] -> ([(Nat, DList Term)], [(Term, Term)])
  candidate is ts = case (is, ts) of
    (i : is, Var j [] : ts) -> first ((j, singleton i) :) $
                               candidate is ts
    (i : is, t : ts)        -> second ((i, t) :) $
                               candidate is ts
    ([],     [])            -> ([], [])
    _                       -> __IMPOSSIBLE__

  bindS binds = parallelS $
    case IntMap.lookupMax binds of
      Nothing       -> []
      Just (max, _) -> for [0 .. max] $ \i ->
        fromMaybe (deBruijnVar i) (IntMap.lookup i binds)

  codomain
    :: Substitution
    -> IntSet  -- Support.
    -> Context -> Context
  codomain s vs =
    mapMaybe (\(i, c) -> if i `IntSet.member` vs
                         then Nothing
                         else Just c) .
    zipWith (\i c -> (i, dropS (i + 1) s `applySubst` c)) [0..]

-- | Like @unifyElims@ but @Γ@ is from the the meta's @MetaInfo@ and
-- the context extension @Δ@ is taken from the @Closure@.
unifyElimsMeta :: MetaId -> Args -> Closure Constraint -> ([(Term,Term)] -> Constraint -> TCM a) -> TCM a
unifyElimsMeta m es_m cl k = ifM (isNothing . optCubical <$> pragmaOptions) (enterClosure cl $ k []) $ do
                  mv <- lookupLocalMeta m
                  enterClosure (getMetaInfo mv) $ \ _ -> do -- mTel ⊢
                  ty <- metaType m
                  mTel0 <- getContextTelescope
                  unless (size mTel0 == size es_m) $ reportSDoc "tc.iapply.ip.meta" 20 $ "funny number of elims" <+> text (show (size mTel0, size es_m))
                  unless (size mTel0 <= size es_m) $ __IMPOSSIBLE__ -- meta has at least enough arguments to fill its creation context.
                  reportSDoc "tc.iapply.ip.meta" 20 $ "ty: " <+> prettyTCM ty

                  -- if we have more arguments we extend the telescope accordingly.
                  TelV mTel1 _ <- telViewUpToPath (size es_m) ty
                  addContext (mTel1 `apply` teleArgs mTel0) $ do
                  mTel <- getContextTelescope
                  reportSDoc "tc.iapply.ip.meta" 20 $ "mTel: " <+> prettyTCM mTel

                  es_m <- return $ take (size mTel) es_m
                  -- invariant: size mTel == size es_m

                  (c,cxt) <- enterClosure cl $ \ c -> (c,) <$> getContextTelescope
                  reportSDoc "tc.iapply.ip.meta" 20 $ prettyTCM cxt

                  addContext cxt $ do

                  reportSDoc "tc.iapply.ip.meta" 20 $ "es_m" <+> prettyTCM es_m

                  reportSDoc "tc.iapply.ip.meta" 20 $ "trying unifyElims"

                  unifyElims (teleArgs mTel) es_m $ \ sigma eqs -> do

                  reportSDoc "tc.iapply.ip.meta" 20 $ "gotten a substitution"

                  reportSDoc "tc.iapply.ip.meta" 20 $ "sigma:" <+> prettyTCM sigma
                  reportSDoc "tc.iapply.ip.meta" 20 $ "sigma:" <+> pretty sigma

                  k eqs (sigma `applySubst` c)
