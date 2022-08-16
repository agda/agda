{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.IApplyConfluence where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Arrow (first,second)

import qualified Data.List as List
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal.Generic
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

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Maybe
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
      modifySignature $ updateDefinition f $ updateTheDef
        $ updateCovering (const [])

      traceCall (CheckFunDefCall (getRange f) f [] False) $
        forM_ cls $ checkIApplyConfluence f
    _ -> return ()

-- | @addClause f (Clause {namedClausePats = ps})@ checks that @f ps@
-- reduces in a way that agrees with @IApply@ reductions. Equivalently,
-- this guarantees that the clauses have the "right faces" when
-- considered as terms of Path type.
checkIApplyConfluence :: QName -> Clause -> TCM ()
checkIApplyConfluence f cl = case cl of
      Clause {clauseBody = Nothing} -> return ()
      Clause {clauseType = Nothing} -> __IMPOSSIBLE__
      cl@Clause { clauseTel = clTel
                , namedClausePats = ps
                , clauseType = Just t
                , clauseBody = Just body
                } -> setCurrentRange (getRange f) $ do
          let
            trhs = unArg t
          reportSDoc "tc.cover.iapply" 40 $ "tel =" <+> prettyTCM clTel
          reportSDoc "tc.cover.iapply" 40 $ "ps =" <+> pretty ps
          ps <- normaliseProjP ps
          forM_ (iApplyVars ps) $ \ i -> do
            unview <- intervalUnview'
            let phi = unview $ IMax (argN $ unview (INeg $ argN $ var i)) $ argN $ var i
            let es = patternsToElims ps
            let lhs = Def f es

            reportSDoc "tc.iapply" 40 $ text "clause:" <+> pretty ps <+> "->" <+> pretty body
            reportSDoc "tc.iapply" 20 $ "body =" <+> prettyTCM body

            addContext clTel $
            -- add context for the user. TODO: The names here seem to be
            -- drawn from the types' telescope so they *suck*; can we
            -- draw them from the patterns instead?
              traceCall (CheckBoundary (getRange f) [] phi lhs body) $
                equalTermOnFace phi trhs lhs body


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
                            unzip $ map (\ (j,t:ts) -> ((j,t),map (,var j) ts)) $ Map.toList $ Map.fromListWith (++) (map (second (:[])) binds')
                          cod   = codomain s (map fst binds) dom
                          binds = map (second (raise (size cod - size vs))) binds''
                          eqs   = map (first  (raise $ size dom - size vs)) $ eqs' ++ concat eqss'
                          s     = bindS binds
                      updateContext s (codomain s (map fst binds)) $ do
                      k s (s `applySubst` eqs)
  where
    candidate :: [Term] -> [Term] -> ([(Nat,Term)],[(Term,Term)])
    candidate (i:is) (Var j []:ts) = first ((j,i):) (candidate is ts)
    candidate (i:is) (t:ts)        = second ((i,t):) (candidate is ts)
    candidate [] [] = ([],[])
    candidate _ _ = __IMPOSSIBLE__


    bindS binds = parallelS (for [0..maximum (-1:map fst binds)] $ (\ i -> fromMaybe (deBruijnVar i) (List.lookup i binds)))

    codomain :: Substitution
             -> [Nat]  -- support
             -> Context -> Context
    codomain s vs cxt = map snd $ filter (\ (i,c) -> i `List.notElem` vs) $ zip [0..] cxt'
     where
      cxt' = zipWith (\ n d -> dropS n s `applySubst` d) [1..] cxt


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
