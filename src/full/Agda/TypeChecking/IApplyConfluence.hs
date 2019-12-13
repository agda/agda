{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.IApplyConfluence where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Arrow (first,second)
import Control.Monad.Reader
import Control.Monad.Trans ( lift )

import Data.Either (lefts)
import qualified Data.List as List
import Data.Monoid (Any(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal.Generic
-- import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.Interaction.Options

import Agda.TypeChecking.Primitive hiding (Nat)
-- import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Conversion (equalTermOnFace)
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
import Agda.Utils.Size
import Agda.Utils.Impossible
import Agda.Utils.Functor


checkIApplyConfluence_ :: QName -> TCM ()
checkIApplyConfluence_ f = whenM (optCubical <$> pragmaOptions) $ do
  -- Andreas, 2019-03-27, iapply confluence should only be checked when --cubical.
  -- See test/Succeed/CheckIApplyConfluence.agda.
  -- We cannot reach the following crash point unless --cubical.
  __CRASH_WHEN__ "tc.cover.iapply.confluence.crash" 666
  reportSDoc "tc.cover.iapply" 10 $ text "Checking IApply confluence of" <+> pretty f
  inConcreteOrAbstractMode f $ \ d -> do
  case theDef d of
    Function{funClauses = cls', funCovering = cls} -> do
      reportSDoc "tc.cover.iapply" 10 $ text "length cls =" <+> pretty (length cls)
      when (null cls && not (null $ concatMap (iApplyVars . namedClausePats) cls')) $
        __IMPOSSIBLE__
      modifySignature $ updateDefinition f $ updateTheDef
        $ updateCovering (const [])

      traceCall (CheckFunDefCall (getRange f) f []) $
        forM_ cls $ checkIApplyConfluence f
    _ -> return ()

-- | @addClause f (Clause {namedClausePats = ps})@ checks that @f ps@
-- reduces in a way that agrees with @IApply@ reductions.
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

            addContext clTel $ equalTermOnFace phi trhs lhs body

            case body of
              MetaV m es_m ->
                caseMaybeM (isInteractionMeta m) (return ()) $ \ ii -> do
                cs' <- do
                  reportSDoc "tc.iapply.ip" 20 $ "clTel =" <+> prettyTCM clTel
                  mv <- lookupMeta m
                  enterClosure (getMetaInfo mv) $ \ _ -> do -- mTel ⊢
                  ty <- getMetaType m
                  mTel <- getContextTelescope
                  reportSDoc "tc.iapply.ip" 20 $ "size mTel =" <+> pretty (size mTel)
                  reportSDoc "tc.iapply.ip" 20 $ "size es_m =" <+> pretty (size es_m)

                  unless (size mTel == size es_m) $ reportSDoc "tc.iapply.ip" 20 $ "funny number of elims" <+> text (show (size mTel, size es_m))
                  unless (size mTel <= size es_m) $ __IMPOSSIBLE__
                  let over = if size mTel == size es_m then NotOverapplied else Overapplied

                  -- extend telescope to handle extra elims
                  TelV mTel1 _ <- telViewUpToPath (size es_m) ty
                  reportSDoc "tc.iapply.ip" 20 $ "mTel1 =" <+> prettyTCM mTel1

                  addContext (mTel1 `apply` teleArgs mTel) $ do
                  mTel <- getContextTelescope

                  addContext clTel $ do -- mTel.clTel ⊢
                    () <- reportSDoc "tc.iapply.ip" 40 $ "mTel.clTel =" <+> (prettyTCM =<< getContextTelescope)
                    forallFaceMaps phi __IMPOSSIBLE__ $ \ alpha -> do
                    -- mTel.clTel' ⊢
                    -- mTel.clTel  ⊢ alpha : mTel.clTel'
                    reportSDoc "tc.iapply.ip" 40 $ "mTel.clTel' =" <+> (prettyTCM =<< getContextTelescope)

                    -- TelV tel _ <- telViewUpTo (size es) ty
                    reportSDoc "tc.iapply.ip" 40 $ "i0S =" <+> pretty alpha
                    reportSDoc "tc.iapply.ip" 20 $ fsep ["es :", pretty es]
                    reportSDoc "tc.iapply.ip" 20 $ fsep ["es_alpha :", pretty (alpha `applySubst` es) ]

                    -- reducing path applications on endpoints in lhs
                    let
                       loop t@(Def _ es) = loop' t es
                       loop t@(Var _ es) = loop' t es
                       loop t@(Con _ _ es) = loop' t es
                       loop t@(MetaV _ es) = loop' t es
                       loop t = return t
                       loop' t es = ignoreBlocking <$> (reduceIApply' (pure . notBlocked) (pure . notBlocked $ t) es)
                    lhs <- liftReduce $ traverseTermM loop (Def f (alpha `applySubst` es))

                    let
                        idG = raise (size clTel) $ (teleElims mTel [])

                    reportSDoc "tc.iapply.ip" 20 $ fsep ["lhs :", pretty lhs]
                    reportSDoc "tc.iapply.ip" 40 $ "cxt1 =" <+> (prettyTCM =<< getContextTelescope)
                    reportSDoc "tc.iapply.ip" 40 $ prettyTCM $ alpha `applySubst` ValueCmpOnFace CmpEq phi trhs lhs (MetaV m idG)

                    unifyElims (teleElims mTel []) (alpha `applySubst` es_m) $ \ sigma eqs -> do
                    -- mTel.clTel'' ⊢
                    -- mTel ⊢ clTel' ≃ clTel''.[eqs]
                    -- mTel.clTel'' ⊢ sigma : mTel.clTel'
                    reportSDoc "tc.iapply.ip" 40 $ "cxt2 =" <+> (prettyTCM =<< getContextTelescope)
                    reportSDoc "tc.iapply.ip" 40 $ "sigma =" <+> pretty sigma
                    reportSDoc "tc.iapply.ip" 20 $ "eqs =" <+> pretty eqs

                    buildClosure $ IPBoundary
                       { ipbEquations = eqs
                       , ipbValue     = sigma `applySubst` lhs
                       , ipbMetaApp   = alpha `applySubst` MetaV m es_m
                       , ipbOverapplied = over
                       }

                    -- WAS:
                    -- fmap (over,) $ buildClosure $ (eqs
                    --                , sigma `applySubst`
                    --                    (ValueCmp CmpEq (AsTermsOf (alpha `applySubst` trhs)) lhs (alpha `applySubst` MetaV m es_m)))

                let f ip = ip { ipClause = case ipClause ip of
                                             ipc@IPClause{ipcBoundary = b}
                                               -> ipc {ipcBoundary = b ++ cs'}
                                             ipc@IPNoClause{} -> ipc}
                modifyInteractionPoints (Map.adjust f ii)
              _ -> return ()


-- | current context is of the form Γ.Δ
unifyElims :: Elims
              -- ^ variables to keep   Γ ⊢ x_n .. x_0 : Γ
           -> Elims
              -- ^ variables to solve  Γ.Δ ⊢ es : Γ
           -> (Substitution -> [(Term,Term)] -> TCM a)
              -- Γ.Δ' ⊢ σ : Γ.Δ
              -- Γ.Δ' new current context.
              -- Γ.Δ' ⊢ [(x = u)]
              -- Γ.Δ', [(x = u)] ⊢ id_g = es[σ] : Γ
           -> TCM a
unifyElims idg es k | Just vs <- allApplyElims idg
                    , Just ts <- allApplyElims es = do
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
                  | otherwise = __IMPOSSIBLE__
  where
    candidate :: [Term] -> [Term] -> ([(Nat,Term)],[(Term,Term)])
    candidate (i:is) (Var j []:ts) = first ((j,i):) (candidate is ts)
    candidate (i:is) (t:ts)        = second ((i,t):) (candidate is ts)
    candidate [] [] = ([],[])
    candidate _ _ = __IMPOSSIBLE__


    bindS binds = parallelS (for [0..maximum (-1:map fst binds)] $ (\ i -> fromMaybe (deBruijnVar i) (List.lookup i binds)))

    codomain :: Substitution
             -> [Nat] -- ^ support
             -> Context -> Context
    codomain s vs cxt = map snd $ filter (\ (i,c) -> i `List.notElem` vs) $ zip [0..] cxt'
     where
      cxt' = zipWith (\ n d -> dropS n s `applySubst` d) [1..] cxt


-- | Like @unifyElims@ but @Γ@ is from the the meta's @MetaInfo@ and
-- the context extension @Δ@ is taken from the @Closure@.
unifyElimsMeta :: MetaId -> Elims -> Closure Constraint -> ([(Term,Term)] -> Constraint -> TCM a) -> TCM a
unifyElimsMeta m es_m cl k = ifM (not . optCubical <$> pragmaOptions) (enterClosure cl $ k []) $ do
                  mv <- lookupMeta m
                  enterClosure (getMetaInfo mv) $ \ _ -> do -- mTel ⊢
                  ty <- getMetaType m
                  mTel0 <- getContextTelescope
                  -- TODO extend telescope to handle extra elims
                  unless (size mTel0 == size es_m) $ reportSDoc "tc.iapply.ip.meta" 20 $ "funny number of elims" <+> text (show (size mTel0, size es_m))
                  unless (size mTel0 <= size es_m) $ __IMPOSSIBLE__
                  TelV mTel1 _ <- telViewUpToPath (size es_m) ty
                  addContext (mTel1 `apply` teleArgs mTel0) $ do
                  mTel <- getContextTelescope
                  (c,cxt) <- enterClosure cl $ \ c -> (c,) <$> getContextTelescope
                  reportSDoc "tc.iapply.ip.meta" 20 $ prettyTCM cxt

                  addContext cxt $ do

                  reportSDoc "tc.iapply.ip.meta" 20 $ "es_m" <+> prettyTCM es_m

                  reportSDoc "tc.iapply.ip.meta" 20 $ "trying unifyElims"

                  unifyElims (teleElims mTel []) es_m $ \ sigma eqs -> do

                  reportSDoc "tc.iapply.ip.meta" 20 $ "gotten a substitution"

                  reportSDoc "tc.iapply.ip.meta" 20 $ "sigma:" <+> prettyTCM sigma
                  reportSDoc "tc.iapply.ip.meta" 20 $ "sigma:" <+> pretty sigma

                  k eqs (sigma `applySubst` c)
