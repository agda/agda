{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Coverage.Cubical where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans ( lift )

import Data.Foldable (for_)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal hiding (DataOrRecord(..))
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Translation.InternalToAbstract (NamedClause(..))

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Rules.LHS (DataOrRecord(..), checkSortOfSplitVar)
import Agda.TypeChecking.Rules.LHS.Problem (allFlexVars)
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.Term (unquoteTactic)

import Agda.TypeChecking.Coverage.Match
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Coverage.SplitClause


import Agda.TypeChecking.Conversion (tryConversion, equalType)
import Agda.TypeChecking.Datatypes (getConForm, getDatatypeArgs)
import {-# SOURCE #-} Agda.TypeChecking.Empty ( checkEmptyTel, isEmptyTel, isEmptyType )
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Telescope.Path
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Warnings

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.WithDefault

import Agda.Utils.Impossible


createMissingIndexedClauses :: QName
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> [(SplitTag,(SplitClause,IInfo))]
                            -> [Clause]
                            -> TCM ([(SplitTag,CoverResult)],[Clause])
createMissingIndexedClauses f n x old_sc scs cs = do
  reflId <- getName' builtinReflId
  let infos = [(c,i) | (SplitCon c, (_,TheInfo i)) <- scs ]
  case scs of
    [(SplitCon c,(_newSc,i@TheInfo{}))] | Just c == reflId -> do
      mc <- createMissingConIdClause f n x old_sc i
      caseMaybe mc (return ([],cs)) $ \ ((sp,tree),cl) -> do
      let res = CoverResult tree (IntSet.singleton (length cs)) [] [cl] IntSet.empty
      return ([(sp,res)],snoc cs cl)
    xs | not $ null infos -> do
         reportSDoc "tc.cover.indexed" 20 $ text "size (xs,infos):" <+> pretty (size xs,size infos)
         reportSDoc "tc.cover.indexed" 20 $ text "xs :" <+> pretty (map fst xs)

         unless (size xs == size infos + 1) $
            reportSDoc "tc.cover.indexed" 20 $ text "missing some infos"
            -- Andrea: what to do when we only managed to build a unification proof for some of the constructors?
         Constructor{conData} <- theDef <$> getConstInfo (fst (head infos))
         Datatype{dataPars = pars, dataIxs = nixs, dataTranspIx} <- theDef <$> getConstInfo conData
         hcomp <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinHComp
         trX <- fromMaybe __IMPOSSIBLE__ <$> pure dataTranspIx
         trX_cl <- createMissingTrXTrXClause trX f n x old_sc
         hcomp_cl <- createMissingTrXHCompClause trX f n x old_sc
         (trees,cls) <- fmap unzip . forM infos $ \ (c,i) -> do
           cl <- createMissingTrXConClause trX f n x old_sc c i
           return $ ((SplitCon c , SplittingDone (size $ clauseTel cl)) , cl)
         let extra = [ (SplitCon trX, SplittingDone $ size $ clauseTel trX_cl)
                                           , (SplitCon hcomp, SplittingDone $ size $ clauseTel hcomp_cl)
                                           ]
                 --  = [ (SplitCon trX, SplittingDone $ size $ clauseTel trX_cl) ]
             extraCl = [trX_cl, hcomp_cl]
                 --  = [trX_cl]
         let clauses = cls ++ extraCl
         let tree = SplitAt ((+(pars+nixs+1)) <$> n) StrictSplit $
                                           trees
                                        ++ extra
             res = CoverResult
               { coverSplitTree      = tree
               , coverUsedClauses    = IntSet.fromList (map (length cs +) [0..length clauses-1])
               , coverMissingClauses = []
               , coverPatterns       = clauses
               , coverNoExactClauses = IntSet.empty
               }
         reportSDoc "tc.cover.indexed" 20 $
           "tree:" <+> pretty tree
         addClauses f clauses
         return $ ([(SplitCon trX,res)],cs++clauses)
--         return $ ([],[])
    xs | otherwise -> return ([],cs)

covFillTele :: QName -> Abs Telescope -> Term -> Args -> Term -> TCM [Term]
covFillTele func tel face d j = do
  ed_f <- liftTCM $ runExceptT $ trFillTel tel face d j
  case ed_f of
    Right d_f -> pure $ map unArg d_f
    Left failed_t -> enterClosure failed_t $ \failed_t -> addContext ("i" :: String, __DUMMY_DOM__) $ do
      typeError . GenericDocError =<< vcat
        [ "Could not generate a transport clause for" <+> prettyTCM func
        , "because a term of type" <+> prettyTCM (unAbs failed_t)
        , "lives in the sort" <+> prettyTCM (getSort (unAbs failed_t)) <+> "and thus can not be transported"
        ]

createMissingTrXTrXClause :: QName -- ^ trX
                            -> QName -- ^ f defined
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> TCM Clause
createMissingTrXTrXClause q_trX f n x old_sc = do
  let
   old_tel = scTel old_sc
   old_ps = fromSplitPatterns $ scPats old_sc
   old_t = fromMaybe __IMPOSSIBLE__ $ scTarget old_sc

  reportSDoc "tc.cover.trx.trx" 20 $ "trX-trX clause for" <+> prettyTCM f
  reportSDoc "tc.cover.trx.trx" 20 $ nest 2 $ vcat $
    [ "old_tel:" <+> prettyTCM old_tel
    , "old_ps :" <+> addContext old_tel (prettyTCM $ patternsToElims old_ps)
    , "old_t  :" <+> addContext old_tel (prettyTCM old_t)
    ]

  -- TODO: redo comments, the strategy changed.
  -- old_tel = Γ1, (x : D η v), Δ
  -- α = boundary(old_ps)
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [ α ↦ (f old_ps)[α] ]

  -- α' = boundary(old_ps[x = pat])
  -- Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0) ⊢ pat := trX p φ (trX q ψ x0) : D η v

  -- Ξ = Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0), Δ[x = pat]

  -- Ξ ⊢ w1 := f old_ps[γ1,x = pat,δ] : old_t[γ1,x = pat,δ] -- the case we are defining. can only be used if specialized.

  -- Ξ ⊢ rhs : old_t[γ1,x = pat,δ] [ α' ↦ w1[α']
                                -- , φ  ↦ w1[φ = i1, p = refl]
                                -- , ψ  ↦ w1[ψ = i1, q = refl]
                                -- ]
  -- Ξ ⊢ q2 := tr (i. Path X(η) (q i0) (p i)) φ q : Path X(η) (q i0) (p i1)
  -- Ξ ⊢ pat_rec[0] = pat : D η v
  -- Ξ ⊢ pat_rec[1] = trX q2 (φ ∧ ψ) x0 : D η v
  -- Ξ ⊢ pat-rec[i] := trX (\ j → p (i ∨ j)) (i ∨ φ) (trX (q2_f i) (ψ ∧ (φ ∨ ~ i)) t)

  -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ
  -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
  -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.

  interval <- elInf primInterval
  iz <- primIZero
  io <- primIOne
  tHComp <- primHComp
  tNeg <- primINeg
  let neg i = pure tNeg <@> i
  let min i j = cl primIMin <@> i <@> j
  let max i j = cl primIMax <@> i <@> j
  let
    old_tel = scTel old_sc
    old_ps' = AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc
    old_ps = pure $ old_ps'
    old_ty = pure $ AbsN (teleNames old_tel) $ fromMaybe __IMPOSSIBLE__ $ scTarget old_sc
  -- old_tel = Γ(x: D η v)Δ
  -- Γ1, (x : D η v)  ⊢ delta = (δ : Δ)
    (gamma1x,delta') = splitTelescopeAt (size old_tel - blockingVarNo x) old_tel
    delta = pure $ AbsN (teleNames gamma1x) $ delta'
    gamma1_size = (size gamma1x - 1)
    (gamma1,ExtendTel dType' _) = splitTelescopeAt gamma1_size gamma1x

  old_sides <- forM old_ps' $ \ ps -> do
    let vs = iApplyVars ps
    let tm = Def f $ patternsToElims ps
    xs <- forM vs $ \ v ->
        -- have to reduce these under the appropriate substitutions, otherwise non-normalizing(?)
          fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
    return $ concatMap (\(v,(l,r)) -> [(tNeg `apply` [argN v],l),(v,r)]) xs
  let
    gamma1ArgNames = teleArgNames gamma1
    deltaArgNames = teleArgNames delta'
  (params,xTel,dT) <- addContext gamma1 $ do
    Just (d, ps, _is) <- getDatatypeArgs . unDom =<< reduce dType'
    def <- getConstInfo d
    let dTy = defType def
    let Datatype{dataSort = s} = theDef def
    TelV tel _ <- telView dTy
    let params = AbsN (teleNames gamma1) ps
        xTel = AbsN (teleNames gamma1) (tel `apply` ps)

    dT <- runNamesT [] $ do
          s <- open $ AbsN (teleNames tel) s
          bindNArg (teleArgNames gamma1) $ \ g1 -> do
          bindNArg (teleArgNames $ unAbsN xTel) $ \ x -> do
          params <- pure params `applyN` (fmap unArg <$> g1)
          x      <- sequence x
          s <- s `applyN` (map (pure . unArg) $ params ++ x)
          pure $ El s $ Def d [] `apply` (params ++ x)
    return $ (params, xTel,dT)

  let
    xTelI = pure $ expTelescope interval <$> xTel
    xTelIArgNames = teleArgNames (unAbsN xTel) -- same names

  -- Γ1, φ, p, ψ, q, x0 ⊢ pat := trX p φ (trX q ψ x0)
  let trX' = bindNArg gamma1ArgNames $ \ g1 -> do
             bindNArg ([defaultArg "phi"] ++ xTelIArgNames) $ \ phi_p -> do
             bindNArg [defaultArg "x0"] $ \ x0 -> do
             param_args <- fmap (map (setHiding Hidden . fmap (unnamed . dotP))) $
               pure params `applyN` (fmap unArg <$> g1)
             (phi:p) <- sequence phi_p
             x0 <- sequence x0
             pure $ DefP defaultPatternInfo q_trX $ param_args ++ p ++ [phi] ++ x0
      trX = (fmap . fmap . fmap) patternToTerm <$> trX'
  let pat' =
            bindN (map unArg gamma1ArgNames) $ \ g1 -> do
            bindN (map unArg $ ([defaultArg "phi"] ++ xTelIArgNames)) $ \ phi_p -> do
            bindN (map unArg $ ([defaultArg "psi"] ++ xTelIArgNames)) $ \ psi_q -> do
            bindN (map unArg $ [defaultArg "x0"]) $ \ x0 -> do
            -- (phi:p) <- sequence phi_p
            -- (psi:q) <- sequence psi_q
            -- x0 <- sequence x0
            let trX = trX' `applyN` g1
            trX `applyN` phi_p `applyN` [trX `applyN` psi_q `applyN` x0]
          --  pure $ trX $ p ++ [phi, defaultArg $ unnamed $ trX $ q ++ [psi] ++ x0]
      pat = (fmap . fmap . fmap . fmap) patternToTerm <$> pat'
  let deltaPat g1 phi p psi q x0 =
        delta `applyN` (g1 ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` (psi:q) `applyN` [x0]])
  -- Ξ
  cTel <- runNamesT [] $
    abstractN (pure gamma1) $ \ g1 -> do
    abstractT "φ" (pure interval) $ \ phi -> do
    abstractN (xTelI `applyN` g1) $ \ p -> do
    abstractT "ψ" (pure interval) $ \ psi -> do
    abstractN (xTelI `applyN` g1) $ \ q -> do
    abstractT "x0" (pure dT `applyN` g1 `applyN` (flip map q $ \ f -> f <@> pure iz)) $ \ x0 -> do
    deltaPat g1 phi p psi q x0

  ps_ty_rhs <- runNamesT [] $ do
    bindN (map unArg gamma1ArgNames) $ \ g1 -> do
    bind "φ" $ \ phi -> do
    bindN (map unArg xTelIArgNames) $ \ p -> do
    bind "ψ" $ \ psi -> do
    bindN (map unArg xTelIArgNames) $ \ q -> do
    bind "x0" $ \ x0 -> do
    bindN (map unArg deltaArgNames) $ \ d -> do
    let
      ps :: NamesT TCM NAPs
      ps = old_ps `applyN` (g1
                          ++ [pat' `applyN` g1 `applyN` (phi:p) `applyN` (psi:q) `applyN` [x0]]
                          ++ d)

      rhsTy = old_ty `applyN` (g1
                          ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` (psi:q) `applyN` [x0]]
                          ++ d)

    xTel <- (open =<<) $ pure xTel `applyN` g1
    q4_f <- (open =<<) $ bind "i" $ \ i -> lamTel $ bind "j" $ \ j -> do
      ty <- bind "i" $ \ _ -> xTel
      face <- max phi $ max (neg j) (neg i)
      base <- map defaultArg <$> appTel (sequence q) j
      u  <- liftM2 (,) (max j psi) $ bind "h" $ \ h -> do
              appTel (sequence p) (min j (min h i))
      Right xs <- lift $ runExceptT $ transpSysTel' False ty [u] face base
      pure $ map unArg xs
    -- Ξ ⊢ pat_rec[0] = pat : D η v
    -- Ξ ⊢ pat_rec[1] = trX q4 (φ ∧ ψ) x0 : D η v
    -- Ξ ⊢ pat-rec[i] := trX (\ j → p (i ∨ j)) (i ∨ φ) (trX (q4_f i) (ψ ∧ (φ ∨ ~ i)) t)
    pat_rec <- (open =<<) $ bind "i" $ \ i -> do
          p_conn <- (mapM open =<<) $ lamTel $ bind "i" $ \ j -> sequence p `appTel` max i j
          q4_f' <- (mapM open =<<) $ absApp <$> q4_f <*> i
          trX `applyN` g1 `applyN` (max i phi:p_conn)
              `applyN` [trX `applyN` g1 `applyN` (min psi (max phi (neg i)):q4_f') `applyN` [x0]]

    let mkBndry args = do
            args1 <- (mapM open =<<) $ (absApp <$> args <*> pure io)
            -- faces ought to be constant on "j"
            faces <- pure (fmap (map fst) old_sides) `applyN` args1
            us <- forM (mapM (map snd) old_sides) $ \ u -> do
                  lam "j" $ \ j -> ilam "o" $ \ _ -> do
                    args <- (mapM open =<<) $ (absApp <$> args <*> j)
                    pure u `applyN` args
            forM (zip faces us) $ \ (phi,u) -> liftM2 (,) (open phi) (open u)
    let mkComp pr = bind "i" $ \ i -> do
          d_f <- (open =<<) $ bind "j" $ \ j -> do
            tel <- bind "j" $ \ j -> delta `applyN` (g1 ++ [pr `applyN` [i,j]])
            face <- min phi psi `max` (min i (max phi psi))
            j <- j
            d <- map defaultArg <$> sequence d
            lift $ covFillTele f tel face d j
          let args = bind "j" $ \ j -> do
                g1 <- sequence g1
                x <- pr `applyN` [i,neg j]
                ys <- absApp <$> d_f <*> neg j
                pure $ g1 ++ x:ys
          ty <- (open =<<) $ bind "j" $ \ j -> do
               args <- (mapM open =<<) $ absApp <$> args <*> j
               fmap unDom $ old_ty `applyN` args
          let face = max i (min phi psi)
          base <- (open =<<) $ do
            args' <- (mapM open =<<) $ absApp <$> args <*> pure iz
            fmap (Def f) $ (fmap patternsToElims <$> old_ps) `applyN` args'
          sys <- mkBndry args
          transpSys ty sys face base

    -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ
    -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
    -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.
    syspsi <- (open =<<) $ lam "i" $ \ i -> ilam "o" $ \ _ -> do
      c <- mkComp $ bindN ["i","j"] $ \ [i,j] -> do
        Abs n (data_ty,lines) <- bind "k" $ \ k -> do
          let phi_k = max phi (neg k)
          let p_k = flip map p $ \ p -> lam "h" $ \ h -> p <@> (min k h)
          data_ty <- pure dT `applyN` g1 `applyN` (flip map p $ \ p -> p <@> k)
          line1 <- trX `applyN` g1 `applyN` (phi_k:p_k) `applyN` [x0]

          line2 <- trX `applyN` g1
                       `applyN` (max phi_k j      : (flip map p_k $ \ p -> lam "h" $ \ h -> p <@> (max h j)))
                       `applyN`
                  [trX `applyN` g1
                       `applyN` (max phi_k (neg j): (flip map p_k $ \ p -> lam "h" $ \ h -> p <@> (min h j)))
                       `applyN` [x0]]
          pure (data_ty,[line1,line2])
        data_ty <- open $ Abs n data_ty
        [line1,line2] <- mapM (open . Abs n) lines
        let sys = [(neg i, lam "k" $ \ k -> ilam "o" $ \ _ -> absApp <$> line2 <*> k)
                  ,(neg j `max` j `max` i `max` phi, lam "k" $ \ k -> ilam "o" $ \ _ -> absApp <$> line1 <*> k)
                  ]
        transpSys data_ty sys (pure iz) x0
      absApp <$> pure c <*> i
    sysphi <- (open =<<) $ lam "i" $ \ i -> ilam "o" $ \ o -> do
      c <- mkComp $ bindN ["i","j"] $ \ _ij -> do
        trX `applyN` g1 `applyN` (psi:q) `applyN` [x0]
      absApp <$> pure c <*> i
    syse <- mkBndry $ bind "j" $ \ _ -> sequence $ g1 ++ [absApp <$> pat_rec <*> pure iz] ++ d
    let sys = syse ++ [(phi,sysphi)] ++ [(psi,syspsi)]
    w0 <- (open =<<) $ do
      let w = mkComp (bindN ["i","j"] $ \ [_i, j] -> absApp <$> pat_rec <*> j)
      absApp <$> w <*> pure iz
    let rhs = hcomp (unDom <$> rhsTy) sys w0
    (,,) <$> ps <*> rhsTy <*> rhs
  let (ps,ty,rhs) = unAbsN $ unAbs $ unAbsN $ unAbs $ unAbsN $ unAbs $ unAbsN $ ps_ty_rhs
  reportSDoc "tc.cover.trx.trx" 20 $ "trX-trX clause for" <+> prettyTCM f
  let c = Clause { clauseLHSRange  = noRange
                 , clauseFullRange = noRange
                 , clauseTel       = cTel
                 , namedClausePats = ps
                 , clauseBody      = Just rhs
                 , clauseType      = Just $ Arg (getArgInfo ty) (unDom ty)
                 , clauseCatchall    = False
                 , clauseExact       = Nothing
                 , clauseRecursive   = Just True
                 , clauseUnreachable = Just False
                 , clauseEllipsis    = NoEllipsis
                 , clauseWhereModule = Nothing
                 }
  debugClause "tc.cover.trx.trx" c
  return $ c
createMissingTrXHCompClause :: QName
                            -> QName
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> TCM Clause
createMissingTrXHCompClause q_trX f n x old_sc = do
  let
   old_tel = scTel old_sc
   old_ps = fromSplitPatterns $ scPats old_sc
   old_t = fromMaybe __IMPOSSIBLE__ $ scTarget old_sc

  reportSDoc "tc.cover.trx.hcomp" 20 $ "trX-hcomp clause for" <+> prettyTCM f
  reportSDoc "tc.cover.trx.hcomp" 20 $ nest 2 $ vcat $
    [ "old_tel:" <+> prettyTCM old_tel
    , "old_ps :" <+> addContext old_tel (prettyTCM $ patternsToElims old_ps)
    , "old_t  :" <+> addContext old_tel (prettyTCM old_t)
    ]

  -- old_tel = Γ1, (x : D η v), Δ
  -- α = boundary(old_ps)
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [ α ↦ (f old_ps)[α] ]

  -- α' = boundary(old_ps[x = pat])
  -- Γ1, φ : I, p : Path X(η) _ v, ψ : I, u : I -> [ψ] → D η (p i0), u0 : D η (p i0) ⊢ pat := trX p φ (hcomp ψ u u0) : D η v

  -- Ξ = Γ1, φ : I, p : Path X(η) _ v, ψ : I, u : ..., u0 : D η (p i0), Δ[x = pat]

  -- Ξ ⊢ w1 := f old_ps[γ1,x = pat,δ] : old_t[γ1,x = pat,δ] -- the case we are defining. can only be used if specialized.

  -- Ξ ⊢ rhs : old_t[γ1,x = pat,δ] [ α' ↦ w1[α']
                                -- , φ  ↦ w1[φ = i1, p = refl]   = f old_ps[γ1,x = hcomp ψ u u0    ,δ]
                                -- , ψ  ↦ w1[ψ = i1]             = f old_ps[γ1,x = trX p φ (u i1 _),δ]
                                -- ]

  -- Ξ ⊢ q2 := tr (i. Path X(η) (q i0) (p i)) φ q : Path X(η) (q i0) (p i1)
  -- Ξ ⊢ pat_rec[0] = pat : D η v
  -- Ξ ⊢ pat_rec[1] = trX q2 (φ ∧ ψ) x0 : D η v
  -- Ξ ⊢ pat-rec[i] := trX (\ j → q (i ∨ j)) (i ∨ φ) (trX (q2_f i) (ψ ∧ (φ ∨ ~ i)) t)

  -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ : Δ[γ1,x = pat_rec[1]]
  -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
  -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.

  q_hcomp <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinHComp
  let
   old_tel = scTel old_sc
   old_ps = fromSplitPatterns $ scPats old_sc
   old_t = fromMaybe __IMPOSSIBLE__ $ scTarget old_sc

  reportSDoc "tc.cover.trx.trx" 20 $ "trX-trX clause for" <+> prettyTCM f
  reportSDoc "tc.cover.trx.trx" 20 $ nest 2 $ vcat $
    [ "old_tel:" <+> prettyTCM old_tel
    , "old_ps :" <+> addContext old_tel (prettyTCM $ patternsToElims old_ps)
    , "old_t  :" <+> addContext old_tel (prettyTCM old_t)
    ]

  -- TODO: redo comments, the strategy changed.
  -- old_tel = Γ1, (x : D η v), Δ
  -- α = boundary(old_ps)
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [ α ↦ (f old_ps)[α] ]

  -- α' = boundary(old_ps[x = pat])
  -- Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0) ⊢ pat := trX p φ (trX q ψ x0) : D η v

  -- Ξ = Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0), Δ[x = pat]

  -- Ξ ⊢ w1 := f old_ps[γ1,x = pat,δ] : old_t[γ1,x = pat,δ] -- the case we are defining. can only be used if specialized.

  -- Ξ ⊢ rhs : old_t[γ1,x = pat,δ] [ α' ↦ w1[α']
                                -- , φ  ↦ w1[φ = i1, p = refl]
                                -- , ψ  ↦ w1[ψ = i1, q = refl]
                                -- ]
  -- Ξ ⊢ q2 := tr (i. Path X(η) (q i0) (p i)) φ q : Path X(η) (q i0) (p i1)
  -- Ξ ⊢ pat_rec[0] = pat : D η v
  -- Ξ ⊢ pat_rec[1] = trX q2 (φ ∧ ψ) x0 : D η v
  -- Ξ ⊢ pat-rec[i] := trX (\ j → p (i ∨ j)) (i ∨ φ) (trX (q2_f i) (ψ ∧ (φ ∨ ~ i)) t)

  -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ
  -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
  -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.

  interval <- elInf primInterval
  iz <- primIZero
  io <- primIOne
  tHComp <- primHComp
  tNeg <- primINeg
  let neg i = pure tNeg <@> i
  let min i j = cl primIMin <@> i <@> j
  let max i j = cl primIMax <@> i <@> j
  let
    old_tel = scTel old_sc
    old_ps' = AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc
    old_ps = pure $ old_ps'
    old_ty = pure $ AbsN (teleNames old_tel) $ fromMaybe __IMPOSSIBLE__ $ scTarget old_sc
  -- old_tel = Γ(x: D η v)Δ
  -- Γ1, (x : D η v)  ⊢ delta = (δ : Δ)
    (gamma1x,delta') = splitTelescopeAt (size old_tel - blockingVarNo x) old_tel
    delta = pure $ AbsN (teleNames gamma1x) $ delta'
    gamma1_size = (size gamma1x - 1)
    (gamma1,ExtendTel dType' _) = splitTelescopeAt gamma1_size gamma1x

  old_sides <- forM old_ps' $ \ ps -> do
    let vs = iApplyVars ps
    let tm = Def f $ patternsToElims ps
    xs <- forM vs $ \ v ->
        -- have to reduce these under the appropriate substitutions, otherwise non-normalizing(?)
          fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
    return $ concatMap (\(v,(l,r)) -> [(tNeg `apply` [argN v],l),(v,r)]) xs
  let
    gamma1ArgNames = teleArgNames gamma1
    deltaArgNames = teleArgNames delta'
  (params,xTel,dT) <- addContext gamma1 $ do
    Just (d, ps, _is) <- getDatatypeArgs . unDom =<< reduce dType'
    def <- getConstInfo d
    let dTy = defType def
    let Datatype{dataSort = s} = theDef def
    TelV tel _ <- telView dTy
    let params = AbsN (teleNames gamma1) ps
        xTel = AbsN (teleNames gamma1) (tel `apply` ps)

    dT <- runNamesT [] $ do
          s <- open $ AbsN (teleNames tel) s
          bindNArg (teleArgNames gamma1) $ \ g1 -> do
          bindNArg (teleArgNames $ unAbsN xTel) $ \ x -> do
          params <- pure params `applyN` (fmap unArg <$> g1)
          x      <- sequence x
          s <- s `applyN` (map (pure . unArg) $ params ++ x)
          pure $ El s $ Def d [] `apply` (params ++ x)
    return $ (params, xTel,dT)

  let
    xTelI = pure $ expTelescope interval <$> xTel
    xTelIArgNames = teleArgNames (unAbsN xTel) -- same names

  -- Γ1, φ, p, ψ, q, x0 ⊢ pat := trX p φ (trX q ψ x0)
  let trX' = bindNArg gamma1ArgNames $ \ g1 -> do
             bindNArg ([defaultArg "phi"] ++ xTelIArgNames) $ \ phi_p -> do
             bindNArg [defaultArg "x0"] $ \ x0 -> do
             param_args <- fmap (map (setHiding Hidden . fmap (unnamed . dotP))) $
               pure params `applyN` (fmap unArg <$> g1)
             (phi:p) <- sequence phi_p
             x0 <- sequence x0
             pure $ DefP defaultPatternInfo q_trX $ param_args ++ p ++ [phi] ++ x0
      trX = (fmap . fmap . fmap) patternToTerm <$> trX'
  let
    hcompD' g1 v =
        bindNArg [argH "psi",argN "u", argN "u0"] $ \ x0 -> do
        x0 <- sequence x0
        Just (LEl l t) <- (toLType =<<) $ pure dT `applyN` g1 `applyN` v
        let ty = map (fmap (unnamed . dotP) . argH) [Level l,t]
        pure $ DefP defaultPatternInfo q_hcomp $ ty ++ x0
  hcompD <- runNamesT [] $
            bindN (map unArg $ gamma1ArgNames) $ \ g1 -> do
            bindN (teleNames $ unAbsN $ xTel) $ \ v -> do
            fmap patternToTerm <$> hcompD' g1 v
  let pat' =
            bindN (map unArg gamma1ArgNames) $ \ g1 -> do
            bindN (map unArg $ ([defaultArg "phi"] ++ xTelIArgNames)) $ \ phi_p -> do
            bindN ["psi","u","u0"] $ \ x0 -> do
            let trX = trX' `applyN` g1
            let p0 = flip map (tail phi_p) $ \ p -> p <@> pure iz
            trX `applyN` phi_p `applyN` [hcompD' g1 p0 `applyN` x0]
      pat = (fmap . fmap . fmap) patternToTerm <$> pat'
  let deltaPat g1 phi p x0 =
        delta `applyN` (g1 ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` x0])
  -- Ξ
  cTel <- runNamesT [] $
    abstractN (pure gamma1) $ \ g1 -> do
    abstractT "φ" (pure interval) $ \ phi -> do
    abstractN (xTelI `applyN` g1) $ \ p -> do
    let p0 = flip map p $ \ p -> p <@> pure iz
    let ty = pure dT `applyN` g1 `applyN` p0
    abstractT "ψ" (pure interval) $ \ psi -> do
    abstractT "u" (pure interval --> pPi' "o" psi (\ _ -> ty)) $ \ u -> do
    abstractT "u0" ty $ \ u0 -> do
    deltaPat g1 phi p [psi,u,u0]

  ps_ty_rhs <- runNamesT [] $ do
    bindN (map unArg gamma1ArgNames) $ \ g1 -> do
    bind "φ" $ \ phi -> do
    bindN (map unArg xTelIArgNames) $ \ p -> do
    bind "ψ" $ \ psi -> do
    bind "u" $ \ u -> do
    bind "u0" $ \ u0 -> do
    bindN (map unArg deltaArgNames) $ \ d -> do
    let
      x0 :: Vars TCM
      x0 = [psi,u,u0]
      ps :: NamesT TCM NAPs
      ps = old_ps `applyN` (g1
                          ++ [pat' `applyN` g1 `applyN` (phi:p) `applyN` x0]
                          ++ d)

      rhsTy = old_ty `applyN` (g1
                          ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` x0]
                          ++ d)

    xTel <- (open =<<) $ pure xTel `applyN` g1
    -- Ξ ⊢ pat-rec[i] := trX .. (hfill ... (~ i))
    pat_rec <- (open =<<) $ bind "i" $ \ i -> do
          let tr x = trX `applyN` g1 `applyN` (phi:p) `applyN` [x]
          let p0 = flip map p $ \ p -> p <@> pure iz
          tr (hcomp (pure dT `applyN` g1 `applyN` p0)
                    [(psi,lam "j" $ \ j -> u <@> (min j (neg i)))
                    ,(i  ,lam "j" $ \ _ -> ilam "o" $ \ _ -> u0)]
                    u0)
    --   args : (i.old_tel)  -> ...
    let mkBndry args = do
            args1 <- (mapM open =<<) $ (absApp <$> args <*> pure io)
            -- faces ought to be constant on "j"
            faces <- pure (fmap (map fst) old_sides) `applyN` args1
            us <- forM (mapM (map snd) old_sides) $ \ u -> do
                  lam "j" $ \ j -> ilam "o" $ \ _ -> do
                    args <- (mapM open =<<) $ (absApp <$> args <*> j)
                    pure u `applyN` args
            forM (zip faces us) $ \ (phi,u) -> liftM2 (,) (open phi) (open u)
    rhs <- do
      d_f <- (open =<<) $ bind "j" $ \ j -> do
        tel <- bind "j" $ \ j -> delta `applyN` (g1 ++ [absApp <$> pat_rec <*> j])
        let face = iz
        j <- j
        d <- map defaultArg <$> sequence d
        lift $ covFillTele f tel face d j
      let args = bind "j" $ \ j -> do
            g1 <- sequence g1
            x <- absApp <$> pat_rec <*> neg j
            ys <- absApp <$> d_f <*> neg j
            pure $ g1 ++ x:ys
      ty <- (open =<<) $ bind "j" $ \ j -> do
           args <- (mapM open =<<) $ absApp <$> args <*> j
           fmap unDom $ old_ty `applyN` args
      let face = pure iz
      othersys <- (open =<<) $ lam "j" $ \ j -> ilam "o" $ \ _ -> do
        args' <- (mapM open =<<) $ absApp <$> args <*> j
        fmap (Def f) $ (fmap patternsToElims <$> old_ps) `applyN` args'
      sys <- mkBndry args
      let
        -- we could specialize all of sysphi/syspsi/base to compute
        -- away trX or the hcomp respectively, should lead to
        -- smaller/more efficient terms.
        --
        -- we could also ditch sysphi completely,
        -- as the computation rule for hcomp would achieve the same.
        sysphi = othersys
        syspsi = othersys
      base <- (open =<<) $ do
        args' <- (mapM open =<<) $ absApp <$> args <*> pure iz
        fmap (Def f) $ (fmap patternsToElims <$> old_ps) `applyN` args'
      transpSys ty ((phi,sysphi):(psi,syspsi):sys) face base
    (,,) <$> ps <*> rhsTy <*> pure rhs
  let (ps,ty,rhs) = unAbsN $ unAbs $ unAbs $ unAbs $ unAbsN $ unAbs $ unAbsN $ ps_ty_rhs
  reportSDoc "tc.cover.trx.hcomp" 20 $ "trX-hcomp clause for" <+> prettyTCM f
  let c = Clause { clauseLHSRange  = noRange
                 , clauseFullRange = noRange
                 , clauseTel       = cTel
                 , namedClausePats = ps
                 , clauseBody      = Just rhs
                 , clauseType      = Just $ Arg (getArgInfo ty) (unDom ty)
                 , clauseCatchall    = False
                 , clauseExact       = Nothing
                 , clauseRecursive   = Just True
                 , clauseUnreachable = Just False
                 , clauseEllipsis    = NoEllipsis
                 , clauseWhereModule = Nothing
                 }
  debugClause "tc.cover.trx.hcomp" c
  return c
createMissingTrXConClause :: QName -- trX
                            -> QName -- f defined
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> QName -- constructor name
                            -> UnifyEquiv
                            -> TCM Clause
createMissingTrXConClause q_trX f n x old_sc c (UE gamma gamma' xTel u v rho tau leftInv) = do
  reportSDoc "tc.cover.trxcon" 20 $ "trX-con clause for" <+> prettyTCM f <+> "with con" <+> prettyTCM c
  reportSDoc "tc.cover.trxcon" 20 $ nest 2 $ vcat $
    [ "gamma" <+> prettyTCM gamma
    , "gamma'" <+> prettyTCM gamma'
    , "xTel" <+> addContext gamma (prettyTCM xTel)
    , "u"  <+> addContext gamma (prettyTCM u)
    , "v"  <+> addContext gamma (prettyTCM v)
    , "rho" <+> addContext gamma' (prettyTCM rho)
    ]

  Constructor{conSrcCon = chead} <- theDef <$> getConstInfo c

  -- = TheInfo $ UE delta1' eqTel (map unArg conIxs) (map unArg givenIxs) rho0 tau leftInv

  -- η : Params_D ⊢ c : (a : Args(η)) → D η (ξ(η,a))

  -- scTel old_sc = Γ1, (x : D η v), Δ
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [α(γ1,x,δ) ↦ e(γ1,x,δ)]

  -- Γ = Γ1, a : Args(η)
  -- Γ ⊢ u = ξ(η,a)
  -- Γ ⊢ c a : D η u

  -- Γ' ⊢ ρ : Γ

  -- Γ' ⊢ u[ρ] = v[ρ] : X(η)[ρ]

  -- Γ' ⊢ c a[ρ] : (D η v)[ρ]

  -- Γ' ⊢ ρx := ρ,x = c a[ρ] : Γ,(x : D η v)

  -- Γ',Δ[ρx] ⊢ old_t[ρx]
  -- Γ',Δ[ρx] ⊢ f old_ps[ρx] : old_t[ρx] [α[ρx] ↦ e[γ1,x,δ][ρx]]

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ τ : Γ'

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ [ρx][τ] = [ρ[τ], x = c a[ρ[τ]]] : Γ,(x : D η v)

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ leftInv : ρ[τ],i1,refl ≡ idS : Γ,(φ : I),(p : Path X(η) u v)

  -- Γ,(φ : I),(p : Path X(η) u v)| (i : I) ⊢ leftInv i : Γ,(φ : I),(p : Path X(η) u v)

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ leftInv i0 = ρ[τ],i1,refl : Γ,(φ : I),(p : Path X(η) u v)
  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ leftInv i1 = γ   ,φ ,p    : Γ,(φ : I),(p : Path X(η) u v)
  --                                 leftInv[φ = i1][i] = idS

  -- Γ,(φ : I),(p : Path X(η) u v),Δ[ρx][τ] ⊢ τ' = liftS |Δ[ρx]| τ : Γ',Δ[ρx]

  -- Γ,(φ : I),(p : Path X(η) u v),Δ[ρx][τ] ⊢
  --            w := f old_ps[γ1[ρ[τ]],x = c a[ρ[τ]],δ] : old_t[ρx][τ'] = old_t[γ1[ρ[τ]],x = c a[ρ[τ]],δ]

  -- Γ,(φ : I),(p : Path X(η) u v),Δ[ρx][τ], α(γ1,x,δ)[ρx][τ'] ⊢ w = e(γ1,x,δ)[ρx][τ']

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ pat := trX p φ (c a) : D η v


  -- Ξ := Γ,(φ : I),(p : Path X(η) u v),(δ : Δ[x = pat])

  -- Ξ ⊢ δ_f[1] = trTel (i. Δ[γ1[leftInv (~ i)], pat[leftInv (~i)]]) φ δ : Δ[ρ[τ], x = c a[ρ[τ]]]

  -- Ξ ⊢ w[δ_f[1]] : old_t[γ1[ρ[τ]],x = c a[ρ[τ]],δ_f[1]]
  -- Ξ, α(γ1,x,δ)[ρx][τ'][δ = δ_f[1]] ⊢ w[δ_f[1]] = e(γ1,x,δ)[ρx][τ'][δ_f[1]]

  -- Ξ, α(γ1[ρ[τ]],c a[ρ[τ]],δ_f[1]) ⊢ w[δ_f[1]] = e(γ1[ρ[τ]],c a[ρ[τ]],δ_f[1])

  -- Recap:
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [α(γ1,x,δ) ↦ e(γ1,x,δ)]
  -- Ξ := Γ,(φ : I),(p : Path X(η) u v),(δ : Δ[x = pat])
  -- Ξ ⊢ δ_f[1] := trTel (i. Δ[γ1[leftInv (~ i)], pat[leftInv (~i)]]) φ δ : Δ[ρ[τ], x = c a[ρ[τ]]]
  -- Γ,(φ : I),(p : Path X(η) u v),Δ[ρx][τ] ⊢
  --            w := f old_ps[γ1[ρ[τ]],x = c a[ρ[τ]],δ] : old_t[ρx][τ'] = old_t[γ1[ρ[τ]],x = c a[ρ[τ]],δ]
  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ pat := trX p φ (c a) : D η v


  -- Ξ ⊢ ?rhs : old_t[γ1,x = pat,δ] [α(γ1,pat,δ) ↦ e(γ1,pat,δ)
  --                               ,φ           ↦ w
  --                               ]

  -- ?rhs := transp (i. old_t[γ1[leftInv i],x = pat[leftInv i], δ_f[~i]]) φ (w[δ_f[1]])

  -- we shall consider α(γ1,pat,δ) = α(γ1[ρ[τ]],c a[ρ[τ]],δ_f[1])
  -- also rather than (p : Path X(η) u v) we'll have (p : I -> X(η)), same as the type of trX.

  iz <- primIZero
  interval <- elInf primInterval
  let
      old_tel = scTel old_sc
      old_ps = pure $ AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc
      old_ty = pure $ AbsN (teleNames old_tel) $ fromMaybe __IMPOSSIBLE__ $ scTarget old_sc
  -- old_tel = Γ(x: D η v)Δ
  -- Γ1, (x : D η v)  ⊢ delta = (δ : Δ)
      (gamma1x,delta') = splitTelescopeAt (size old_tel - blockingVarNo x) old_tel
  let
    gammaArgNames = teleArgNames gamma
    deltaArgNames = teleArgNames delta'
  let
    xTelI = pure $ AbsN (teleNames gamma) $ expTelescope interval xTel
    delta = pure $ AbsN (teleNames gamma1x) $ delta'
    gamma1_size = (size gamma1x - 1)
    (gamma1,ExtendTel dType' _) = splitTelescopeAt gamma1_size gamma1x
  params <- addContext gamma1 $ do
    Just (_d, ps, _is) <- getDatatypeArgs . unDom =<< reduce dType'
    return $ AbsN (teleNames gamma1) ps
  -- Γ, φ , p ⊢ pat := trX p φ (c a)
  let pat' =
            bindNArg gammaArgNames $ \ g1_args -> do
            bindNArg ([defaultArg "phi"] ++ teleArgNames xTel) $ \ phi_p -> do
            let (g1,args) = splitAt gamma1_size g1_args
            (phi:p) <- sequence phi_p
            args <- sequence args
            let cargs = defaultArg $ unnamed $ ConP chead noConPatternInfo args
            -- Amy (2022-11-06): Set the parameters to quantity-0.
            param_args <- fmap (map (setQuantity (Quantity0 Q0Inferred) . setHiding Hidden . fmap (unnamed . dotP))) $
              pure params `applyN` take gamma1_size (fmap unArg <$> g1_args)
            pure $ DefP defaultPatternInfo q_trX $ param_args ++ p ++ [phi,cargs]
      pat = (fmap . fmap) patternToTerm <$> pat'
      pat_left' = (fmap . fmap) (Abs "i" . (applySubst leftInv)) <$> pat
      g1_left' = bindN (map unArg gammaArgNames) $ \ g1_args -> do
                bindN (map unArg $ [defaultArg "phi"] ++ teleArgNames xTel) $ \ phi_p -> do
                g1 <- sequence $ take gamma1_size g1_args :: NamesT TCM [Term]
                pure $ Abs "i" (applySubst leftInv g1)

  gamma <- return $ pure gamma
  let deltaPat g1_args phi p =
        delta `applyN` (take gamma1_size g1_args ++ [pat `applyN` g1_args `applyN` (phi:p)])
  let neg i = cl primINeg <@> i
  -- Ξ
  cTel <- runNamesT [] $
    abstractN gamma $ \ g1_args -> do
    abstractT "φ" (pure interval) $ \ phi -> do
    abstractN (xTelI `applyN` g1_args) $ \ p -> do
    deltaPat g1_args phi p
  ps_ty_rhs <- runNamesT [] $ do
    bindN (map unArg gammaArgNames) $ \ g1_args -> do
    bind "phi" $ \ phi -> do
    bindN (teleNames xTel) $ \ p -> do
    bindN (map unArg $ deltaArgNames) $ \ d -> do
    let
      g1_left = g1_left' `applyN` g1_args `applyN` (phi:p)
      pat_left = pat_left' `applyN` g1_args `applyN` (phi:p)
      g1 :: Vars TCM
      g1 = take gamma1_size g1_args

      args :: Vars TCM
      args = drop gamma1_size g1_args

      ps :: NamesT TCM NAPs
      ps = old_ps `applyN` (g1 ++ [pat' `applyN` g1_args `applyN` (phi:p)] ++ d)

      rhsTy = old_ty `applyN` (g1 ++ [pat `applyN` g1_args `applyN` (phi:p)] ++ d)

    -- (i. Δ[γ1[leftInv (~ i)], pat[leftInv (~i)]])
    delta_f <- (open =<<) $ bind "i" $ \ i -> do
      let ni = neg i
      dargs <- (mapM open =<<) $ do
        xs <- absApp <$> g1_left <*> ni
        y <- absApp <$> pat_left <*> ni
        return $ xs ++ [y]
      delta `applyN` dargs

    --  trFillTel (i. Δ[γ1[leftInv (~ i)], pat[leftInv (~i)]]) φ δ
    d_f <- (open =<<) $ bind "i" $ \ i -> do
      delta_f <- delta_f
      phi <- phi
      d <- map defaultArg <$> sequence d
      i <- i
      lift $ covFillTele f delta_f phi d i

    -- w = Def f (old_ps[g1_left[i],pat_left[i],d_f[~ i]])
    w <- (open =<<) $ bind "i" $ \ i -> do
      psargs <- (mapM open =<<) $ do
        xs <- absApp <$> g1_left <*> i
        y <- absApp <$> pat_left <*> i
        zs <- absApp <$> d_f <*> neg i
        return $ xs ++ [y] ++ zs
      ps <- (fmap patternsToElims <$> old_ps) `applyN` psargs
      pure $ Def f ps


    -- (i. old_t[γ1[leftInv i],x = pat[leftInv i], δ_f[~i]])
    ty <- (open =<<) $ bind "i" $ \ i -> do
      tyargs <- (mapM open =<<) $ do
        xs <- absApp <$> g1_left <*> i
        y <- absApp <$> pat_left <*> i
        zs <- absApp <$> d_f <*> neg i
        return $ xs ++ [y] ++ zs
      fmap unDom $ old_ty `applyN` tyargs

    sys <- do
      sides <- do
        neg <- primINeg
        io <- primIOne
        vs <- iApplyVars <$> ps
        tm <- w
        xs <- forM vs $ \ v ->
            -- have to reduce these under the appropriate substitutions, otherwise non-normalizing(?)
              fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
        return $ concatMap (\(v,(l,r)) -> [(neg `apply` [argN v],l),(v,r)]) xs
      forM sides $ \ (psi,u') -> do
        u' <- open u'
        u <- lam "i" $ \ i -> ilam "o" $ \ o -> absApp <$> u' <*> i
        (,) <$> open psi <*> open u

    let rhs = transpSys ty sys phi (absApp <$> w <*> pure iz)

    (,,) <$> ps <*> rhsTy <*> rhs

  let (ps,ty,rhs) = unAbsN $ unAbsN $ unAbs $ unAbsN $ ps_ty_rhs
  qs <- mapM (fmap (fromMaybe __IMPOSSIBLE__) . getName') [builtinINeg, builtinIMax, builtinIMin]
  rhs <- addContext cTel $
           locallyReduceDefs (OnlyReduceDefs (Set.fromList $ q_trX : qs)) $ normalise rhs
  let cl = Clause { clauseLHSRange  = noRange
                  , clauseFullRange = noRange
                  , clauseTel       = cTel
                  , namedClausePats = ps
                  , clauseBody      = Just rhs
                  , clauseType      = Just $ Arg (getArgInfo ty) (unDom ty)
                  , clauseCatchall    = False
                  , clauseExact       = Nothing
                  , clauseRecursive   = Just True
                  , clauseUnreachable = Just False
                  , clauseEllipsis    = NoEllipsis
                  , clauseWhereModule = Nothing
                  }


  debugClause "tc.cover.trxcon" cl

  reportSDoc "tc.cover.trxcon" 20 $ vcat $
    [ "clause:"
    ,  nest 2 $ prettyTCM . QNamed f $ cl
    ]

  let mod =
        setRelevance Irrelevant $  -- See #5611.
        getModality $ fromMaybe __IMPOSSIBLE__ $ scTarget old_sc
  -- we follow what `cover` does when updating the modality from the target.
  applyModalityToContext mod $ do
    unlessM (asksTC hasQuantity0) $ do
    reportSDoc "tc.cover.trxcon" 20 $ text "testing usable at mod: " <+> pretty mod
    addContext cTel $ usableAtModality IndexedClause mod rhs

  return cl

-- | If given @TheInfo{}@ then assumes "x : Id u v" and
--   returns both a @SplittingDone@ for conId, and the @Clause@ that covers it.
createMissingConIdClause :: QName         -- ^ function being defined
                         -> Arg Nat       -- ^ @covSplitArg@ index
                         -> BlockingVar   -- ^ @x@ variable being split on.
                         -> SplitClause   -- ^ clause before split
                         -> IInfo         -- ^ info from unification
                         -> TCM (Maybe ((SplitTag,SplitTree),Clause))
createMissingConIdClause f _n x old_sc (TheInfo info) = setCurrentRange f $ do
  let
    -- iΓ'
    itel = infoTel
    -- with 3 params, reflId : Id A u u -- no arguments.
    -- iΓ' ⊢ iρ : Γ
    --
    -- Δ = Γ,φ,(p : u ≡ v) ⊢ iτ : iΓ'
    -- ρ = iρ
    -- τ = iτ
    irho = infoRho info
    itau = infoTau info
    ileftInv = infoLeftInv info
  interval <- elInf primInterval
  tTrans  <- primTrans
  tComp  <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinComp
  conId <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinConId
  let bindSplit (tel1,tel2) = (tel1,AbsN (teleNames tel1) tel2)
  let
      old_tel = scTel old_sc

  -- old_tel = Γ(x: Id A u v)Δ
  -- Γ(x: Id A u v)Δ ⊢ old_t
  -- Γ ⊢ hdelta = (x : Id A u v)(δ : Δ)
      pair@(_gamma,_hdelta@(ExtendTel hdom delta)) = splitTelescopeAt (size old_tel - (blockingVarNo x + 1)) old_tel
      (gamma,hdelta) = bindSplit pair
      old_t  = AbsN (teleNames old_tel) $ fromJust $ scTarget old_sc
      old_ps = AbsN (teleNames old_tel) $ patternsToElims $ fromSplitPatterns $ scPats old_sc
      old_ps' = AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc

  params <- runNamesT [] $ do
    hdelta <- open hdelta
    bindN (teleNames gamma) $ \ args -> do
       hdelta@(ExtendTel hdom _) <- applyN hdelta args
       Def _Id es@[_,_,_,_] <- reduce $ unEl $ unDom hdom
       return $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

  working_tel <- runNamesT [] $ do
    hdelta <- open hdelta
    params <- open params
    abstractN (pure gamma) $ \ args -> do
      pTel <- open =<< (lift $ pathTelescope (infoEqTel info) (map defaultArg $ infoEqLHS info) (map defaultArg $ infoEqRHS info))
      abstractN (pure (telFromList [defaultDom ("phi",interval)] :: Telescope)) $ \ [phi] ->
        abstractN pTel $ \ [p] -> do
          [l,bA,x,y] <- mapM open =<< applyN params args
          apply1 <$> applyN hdelta args <*> (cl primConId <#> l <#> bA <#> x <#> y <@> phi <@> p)
  -- working_tel ⊢ i. γ[leftInv i]
  (gamma_args_left :: Abs [Term], con_phi_p_left :: Abs Term) <- fmap (raise (size delta) . unAbsN) . runNamesT [] $ do
    params <- open params
    bindN (teleNames gamma ++ ["phi","p"]) $ \ args' -> do
      let (args,[phi,p]) = splitAt (size gamma) args'
      [l,bA,x,y] <- mapM open =<< applyN params args
      gargs <- Abs "i" . applySubst ileftInv <$> sequence args
      con_phi_p <- Abs "i" . applySubst ileftInv <$> do
        (cl primConId <#> l <#> bA <#> x <#> y <@> phi <@> p)
      return (gargs,con_phi_p)
  ps <- fmap unAbsN . runNamesT [] $ do
    old_ps' <- open $ old_ps'
    params <- open params
    bindN (teleNames working_tel) $ \ (wargs :: [NamesT TCM Term]) -> do
      let (g,phi:p:d) = splitAt (size gamma) $ telePatterns working_tel []
      params <- map (argH . unnamed . dotP) <$> applyN params (take (size gamma) wargs)
      let x = DefP defaultPatternInfo conId $ params ++ [phi,p]
      args <- open $ map namedArg g ++ [x] ++ map namedArg d
      applyN' old_ps' args
  -- tel = Γ',Δ[ρ,x = refl]
  -- Γ' ⊢ ρ : Γ
  -- Γ' ⊢ u[ρ] = v[ρ] : A[ρ]

  -- Γ' ⊢ ρ,x=refl : Γ,(x : Id A u v)

  -- Γ',Δ[ρ,x = refl] ⊢ old_t[ρ,x=refl] = Δ₂ -> t
  -- Γ',Δ[ρ,x = refl] ⊢ f old_ps[ρ,x = refl] : old_t[ρ,x = refl]
  -- Γ,(φ : I),(p : Path A u v) ⊢ τ : Γ'

  -- Γ' ⊢ [ρ,x = refl u[ρ]] : Γ,(x : Id A u v)

  -- Γ,(φ : I),(p : Path A u v) ⊢ [ρ,x = refl u[ρ]][τ] = [ρ[τ], x = refl u[ρ[τ]]] : Γ,(x : Id A u v)

  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv : ρ[τ],i1,refl ≡ idS : Γ,(φ : I),(p : Path A u v)

  -- Γ,(φ : I),(p : Path A u v)| (i : I) ⊢ leftInv i : Γ,(φ : I),(p : Path A u v)

  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i0 = ρ[τ],i1,refl : Γ,(φ : I),(p : Path A u v)
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i1 = γ   ,φ ,p : Γ,(φ : I),(p : Path A u v)
  --                      leftInv[φ = i1][i] = idS

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢ τ' = liftS |Δ[ρ,x = refl]| τ : Γ',Δ[ρ,x = refl]

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢
  --            w = f old_ps[ρ[τ],x = refl u[ρ[τ]],δ] : old_t[ρ,x = refl][τ'] = old_t[ρ[τ],x = refl u[ρ[τ]],δ]

  -- Γ,(φ : I),(p : Path A u v) | (i : I) ⊢ μ = ⟨φ,p⟩[leftInv (~i)] : (Id A u v)[γ[leftInv (~ i)]]
  --                                     μ[0] = ⟨ φ             , p    ⟩
  --                                     μ[1] = ⟨ 1             , refl ⟩

  -- Γ,(φ : I),(p : Path A u v),(δ : Δ[x = ⟨ φ , p ⟩]) ⊢
  --         δ_f[1] = vecTransp (i. Δ[γ[leftInv (~ i)], ⟨φ,p⟩[leftInv (~i)]]) φ δ : Δ[ρ[τ], x = refl u[ρ[τ]]]

  -- Γ,(φ : I),(p : Path A u v),(δ : Δ[x = ⟨ φ , p ⟩]) ⊢ w[δ_f[1]] : old_t[ρ[τ],x = refl u[ρ[τ]],δ_f[1]]
  -- Γ,(φ : I),(p : Path A u v),Δ[x = ⟨ φ , p ⟩] ⊢ rhs = transp (i. old_t[γ[leftInv i],x = ⟨φ,p⟩[leftInv i], δ_f[~i]]) φ (w[δ_f[1]]) : old_t[γ,x = ⟨ φ , p ⟩,δ]
  let
      getLevel t = do
        s <- reduce $ getSort t
        case s of
          Type l -> pure (Level l)
          s      -> do
            reportSDoc "tc.cover.hcomp" 20 $ text "getLevel, s = " <+> prettyTCM s
            typeError . GenericDocError =<<
                    (text "The sort of" <+> prettyTCM t <+> text "should be of the form \"Set l\"")
  (ty,rhs) <- addContext working_tel $ runNamesT [] $ do
    let
        raiseFrom :: Subst a => Telescope -> a -> a
        raiseFrom tel x = raise (size working_tel - size tel) x
        all_args = teleArgs working_tel :: Args
        (gamma_args,phi:p:delta_args) = splitAt (size gamma) all_args
    old_t <- open $ raiseFrom EmptyTel old_t
    old_ps <- open $ raiseFrom EmptyTel old_ps
    delta_args <- open delta_args
    gamma_args_left <- open gamma_args_left
    con_phi_p_left <- open con_phi_p_left
    hdelta <- open $ raiseFrom gamma hdelta
    delta_f <- bind "i" $ \ i -> do
      apply1 <$> applyN' hdelta (lazyAbsApp <$> gamma_args_left <*> (cl primINeg <@> i)) <*> (lazyAbsApp <$> con_phi_p_left <*> (cl primINeg <@> i))
    delta_f <- open delta_f
    [phi,p] <- mapM (open . unArg) [phi,p]
    delta_args_f <- bind "i" $ \ i -> do

      m <- trFillTel' True <$> delta_f <*> phi <*> delta_args <*> i
      either __IMPOSSIBLE__ id <$> (lift $ runExceptT m)
    delta_args_f <- open delta_args_f
    old_t_f <- (open =<<) $ bind "i" $ \ i -> do
      g <- lazyAbsApp <$> gamma_args_left <*> i
      x <- lazyAbsApp <$> con_phi_p_left <*> i
      d <- lazyAbsApp <$> delta_args_f <*> (cl primINeg <@> i)
      args <- open $ g ++ [x] ++ map unArg d
      applyN' old_t args
    w <- (open =<<) $ bind "i" $ \ i -> do
      g <- lazyAbsApp <$> gamma_args_left <*> i
      x <- lazyAbsApp <$> con_phi_p_left <*> i
      d <- lazyAbsApp <$> delta_args_f <*> (cl primINeg <@> i)
      args <- open $ g ++ [x] ++ map unArg d
      Def f <$> applyN' old_ps args

    ps <- open ps
    max <- primIMax
    iz <- primIZero
    alphas <- (open =<<) $ do
      vs <- iApplyVars <$> ps
      neg <- primINeg
      zero <- primIZero
      return $ foldr (\ x r -> max `apply` [argN $ max `apply` [argN x, argN (neg `apply` [argN x])], argN r]) zero $ map var vs
    sides <- (open =<<) $ do
      neg <- primINeg
      io <- primIOne
      bind "i" $ \ i -> do
        vs <- iApplyVars <$> ps
        tm <- lazyAbsApp <$> w <*> i
        xs <- forM vs $ \ v ->
          -- have to reduce these under the appropriate substitutions, otherwise non-normalizing
          fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
        phiv <- fromMaybe __IMPOSSIBLE__ . deBruijnView <$> phi
        -- extra assumption: phi |- w i = w 0, otherwise we need [ phi -> w 0 ] specifically
        tm_phi <- reduce $ inplaceS phiv io `applySubst` tm
        phi <- phi
        return $ (phi,tm_phi) : concatMap (\(v,(l,r)) -> [(neg `apply` [argN v],l),(v,r)]) xs

    let imax i j = apply max $ map argN [i,j]
    tPOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
    let
      pOr l ty phi psi u0 u1 = do
          [phi,psi] <- mapM open [phi,psi]
          pure tPOr <#> l
                    <@> phi <@> psi
                    <#> (ilam "o" $ \ _ -> ty) <@> noilam u0 <@> u1

      noilam u = do
         u <- open u
         ilam "o" $ \ _ -> u

      combine l ty [] = __IMPOSSIBLE__
      combine l ty [(psi,u)] = noilam u
      combine l ty ((psi,u):xs) = pOr l ty psi (foldr imax iz (map fst xs)) u (combine l ty xs)

    let ty i = lazyAbsApp <$> old_t_f <*> i
    l <- (open =<<) $ lam "i" $ \ i -> do
           t <- unDom <$> ty i
           lift $ getLevel t
    ((,) <$> ty (cl primIOne) <*>) $ do
         n <- length . unAbs <$> sides
         -- TODO don't comp if the family and the sides "j. [ α ↦ u ]" are constant?
         if n > 1 then
           pure tComp <#> l <@> (lam "i" $ \ i -> unEl . unDom <$> ty i)
                <@> (cl primIMax <@> phi <@> alphas)
                <@> (lam "i" $ \ i -> combine (l <@> i) (unEl . unDom <$> ty i) =<< (lazyAbsApp <$> sides <*> i))
                <@> (lazyAbsApp <$> w <*> primIZero)
         else
           pure tTrans <#> l <@> (lam "i" $ \ i -> unEl . unDom <$> ty i)
                <@> phi
                <@> (lazyAbsApp <$> w <*> primIZero)

  reportSDoc "tc.cover.conid" 20 $ text "conid case for" <+> text (show f)
  reportSDoc "tc.cover.conid" 20 $ text "tel =" <+> prettyTCM working_tel
  reportSDoc "tc.cover.conid" 25 $ addContext working_tel $ prettyTCM rhs

  let cl =   Clause { clauseLHSRange  = noRange
                    , clauseFullRange = noRange
                    , clauseTel       = working_tel
                    , namedClausePats = ps
                    , clauseBody      = Just $ rhs
                    , clauseType      = Just $ Arg (domInfo ty) (unDom ty)
                    , clauseCatchall    = False
                    , clauseUnreachable = Just False  -- missing, thus, not unreachable
                    , clauseRecursive   = Just False
                    , clauseEllipsis    = NoEllipsis
                    , clauseExact       = Nothing
                    , clauseWhereModule = Nothing
                    }
  addClauses f [cl]
  return $ Just ((SplitCon conId,SplittingDone (size working_tel)),cl)
createMissingConIdClause f n x old_sc NoInfo = return Nothing


{-
  OLD leftInv case
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv : ρ[τ] ≡ wkS 2 : Γ
  -- Γ,(φ : I),(p : Path A u v)(i : I) ⊢ leftInv i : Γ
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i0 = ρ[τ] : Γ
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i1 = wkS 2 : Γ
  -- leftInv[φ = i1][i] = wkS 2

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢ τ' = liftS |Δ[ρ,x = refl]| τ : Γ',Δ[ρ,x = refl]

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢ w = f old_ps[ρ,x = refl][τ'] : old_t[ρ,x = refl][τ']

  -- Γ,(φ : I),(p : Path A u v) | (i : I) ⊢ μ = ⟨ (φ ∨ ~ i) , (\ j → p (i ∧ j)) ⟩ : Id A u (p i) =?= (Id A u v)[leftInv (~ i)]
                                  μ[0] = ⟨ 1 , (\ _ → u[ρ[τ]]) ⟩
                                  μ[1] = ⟨ φ , p               ⟩
  -- Γ,(φ : I),(p : Path A u v),(δ : Δ[x = ⟨ φ , p ⟩]) ⊢ vecTransp (i. Δ[leftInv (~ i),μ[i]]) φ δ : Δ[ρ[τ], x = refl u[ρ[τ]]]
-}

-- | Append an hcomp clause to the clauses of a function.
createMissingHCompClause
  :: QName
       -- ^ Function name.
  -> Arg Nat -- ^ index of hcomp pattern
  -> BlockingVar -- ^ Blocking var that lead to hcomp split.
  -> SplitClause -- ^ Clause before the hcomp split
  -> SplitClause
       -- ^ Clause to add.
  -> [Clause]
   -> TCM ([(SplitTag,CoverResult)], [Clause])
createMissingHCompClause f n x old_sc (SClause tel ps _sigma' _cps (Just t)) cs = setCurrentRange f $ do
  reportSDoc "tc.cover.hcomp" 20 $ addContext tel $ text "Trying to create right-hand side of type" <+> prettyTCM t
  reportSDoc "tc.cover.hcomp" 30 $ addContext tel $ text "ps = " <+> prettyTCMPatternList (fromSplitPatterns ps)
  reportSDoc "tc.cover.hcomp" 30 $ text "tel = " <+> prettyTCM tel

  io      <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIOne
  iz      <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIZero
  let
    cannotCreate :: MonadTCError m => Doc -> Closure (Abs Type) -> m a
    cannotCreate doc t = do
      typeError . SplitError $ CannotCreateMissingClause f (tel,fromSplitPatterns ps) doc t
  let old_ps = patternsToElims $ fromSplitPatterns $ scPats old_sc
      old_t  = fromJust $ scTarget old_sc
      old_tel = scTel old_sc
      -- old_tel = Γ(x:H)Δ
      -- Γ(x:H)Δ ⊢ old_t
      -- vs = iApplyVars old_ps
      -- [ α ⇒ b ] = [(i,f old_ps (i=0),f old_ps (i=1)) | i <- vs]

      -- Γ(x:H)(δ : Δ) ⊢ [ α ⇒ b ]
      -- Γ(x:H)Δ ⊢ f old_ps : old_t [ α ⇒ b ]
      -- Γ,φ,u,u0,Δ(x = hcomp φ u u0) ⊢ rhs_we_define : (old_t[ α ⇒ b ])(x = hcomp φ u u0)

      -- Extra assumption:
      -- tel = Γ,φ,u,u0,Δ(x = hcomp φ u u0),Δ'
      -- ps = old_ps[x = hcomp φ u u0],ps'
      -- with Δ' and ps' introduced by fixTarget.
      -- So final clause will be:
      -- tel ⊢ ps ↦ rhs_we_define{wkS ..} ps'
      getLevel t = do
        s <- reduce $ getSort t
        case s of
          Type l -> pure (Level l)
          s      -> do
            reportSDoc "tc.cover.hcomp" 20 $ text "getLevel, s = " <+> prettyTCM s
            typeError . GenericDocError =<<
                    (text "The sort of" <+> prettyTCM t <+> text "should be of the form \"Set l\"")

      -- Γ ⊢ hdelta = (x : H)(δ : Δ)
      (gamma,hdelta@(ExtendTel hdom delta)) = splitTelescopeAt (size old_tel - (blockingVarNo x + 1)) old_tel

      -- Γ,φ,u,u0,Δ(x = hcomp φ u u0) ⊢
      (working_tel,_deltaEx) = splitTelescopeAt (size gamma + 3 + size delta) tel

      -- Γ,φ,u,u0,(x:H)(δ : Δ) ⊢ rhoS : Γ(x:H)(δ : Δ)
      {- rhoS = liftS (size hdelta) $ raiseS 3 -}
      vs = iApplyVars (scPats old_sc)

  -- Γ(x:H)(δ : Δ) ⊢ [ α ⇒ b ] = [(i,f old_ps (i=0),f old_ps (i=1)) | i <- vs]
  alphab <- forM vs $ \ i -> do
               let
                 -- Γ(x:H)(δ : Δ) ⊢
                 tm = Def f old_ps
               -- TODO only reduce IApply _ _ (0/1), as to avoid termination problems
               (l,r) <- reduce (inplaceS i iz `applySubst` tm, inplaceS i io `applySubst` tm)
               return $ (var i, (l, r))



  cl <- do
    (ty,rhs) <- addContext working_tel $ do
      -- Γ(x:H)Δ ⊢ g = f old_ps : old_t [ α ⇒ b ]
      -- Γ(x:H)(δ : Δ) ⊢ [ α ⇒ b ]
      -- Γ,φ,u,u0 ⊢ Δf = i.Δ[x = hfill φ u u0 i]
      -- Γ,φ,u,u0,δ : Δ(x = hcomp φ u u0) ⊢ δ_fill     = i.tFillTel (i. Δf[~i]) δ (~ i) : i.Δf[i]
      -- Γ,φ,u,u0,δ : Δ(x = hcomp φ u u0) ⊢ old_t_fill = i.old_t[x = hfill φ u u0 i, δ_fill[i]]
      -- Γ,φ,u,u0,δ : Δ(x = hcomp φ u u0) ⊢ comp (\ i. old_t_fill[i])
      --                 (\ i. [ φ ↦ g[x = hfill φ u u0 i,δ_fill[i]] = g[u i,δ_fill[i]]
      --                         α ↦ b[x = hfill φ u u0 i,δ_fill[i]]
      --                        ])
      --                 (g[x = u0,δ_fill[0]]) : old_t[x = hcomp φ u u0,δ]

      runNamesT [] $ do
          tPOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
          tIMax <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIMax
          tIMin <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIMin
          tINeg <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinINeg
          tHComp <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinHComp
          tTrans <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinTrans
          extra_ps <- open $ patternsToElims $ fromSplitPatterns $ drop (length old_ps) ps
          let
            ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
            trFillTel' a b c d = do
              m <- trFillTel <$> a <*> b <*> c <*> d
              x <- lift $ runExceptT m
              case x of
                Left bad_t -> cannotCreate "Cannot transport with type family:" bad_t
                Right args -> return args
          comp <- mkCompLazy "hcompClause"
          let
            hcomp la bA phi u u0 = pure tHComp <#> la <#> bA
                                               <#> phi
                                               <@> u
                                               <@> u0

            hfill la bA phi u u0 i = hcomp la bA
                                               (pure tIMax <@> phi <@> (pure tINeg <@> i))
                                               (lam "j" $ \ j -> pure tPOr <#> la <@> phi <@> (pure tINeg <@> i) <#> ilam "o" (\ _ -> bA)
                                                     <@> ilam "o" (\ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                     <@> ilam "o" (\ _ -> u0)
                                                   )
                                               u0
          -- Γ,φ,u,u0,(δ : Δ(x = hcomp φ u u0)) ⊢ hcompS : Γ(x:H)(δ : Δ)
          hcompS <- lift $ do
            hdom <- pure $ raise 3 hdom
            let
              [phi,u,u0] = map (pure . var) [2,1,0]
              htype = pure $ unEl . unDom $ hdom
              lvl = getLevel $ unDom hdom
            hc <- pure tHComp <#> lvl <#> htype
                                      <#> phi
                                      <@> u
                                      <@> u0
            return $ liftS (size delta) $ hc `consS` raiseS 3
          -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ raise 3+|Δ| hdom
          hdom <- pure $ raise (3+size delta) hdom
          htype <- open $ unEl . unDom $ hdom
          lvl <- open =<< (lift . getLevel $ unDom hdom)

          -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢
          [phi,u,u0] <- mapM (open . raise (size delta) . var) [2,1,0]
          -- Γ,x,Δ ⊢ f old_ps
          -- Γ ⊢ abstract hdelta (f old_ps)
          g <- open $ raise (3+size delta) $ abstract hdelta (Def f old_ps)
          old_t <- open $ raise (3+size delta) $ abstract hdelta (unDom old_t)
          let bapp a x = lazyAbsApp <$> a <*> x
          (delta_fill :: NamesT TCM (Abs Args)) <- (open =<<) $ do
            -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ x.Δ
            delta <- open $ raise (3+size delta) delta
            -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ i.Δ(x = hfill phi u u0 (~ i))
            deltaf <- open =<< bind "i" (\ i ->
                           (delta `bapp` hfill lvl htype phi u u0 (ineg i)))
            -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ Δ(x = hcomp phi u u0) = Δf[0]
            args <- (open =<<) $ teleArgs <$> (lazyAbsApp <$> deltaf <*> pure iz)
            bind "i" $ \ i -> addContext ("i" :: String) $ do -- for error messages.
              -- Γ,φ,u,u0,Δ(x = hcomp phi u u0),(i:I) ⊢ ... : Δ(x = hfill phi u u0 i)
              trFillTel' deltaf (pure iz) args (ineg i)
          let
            apply_delta_fill i f = apply <$> f <*> (delta_fill `bapp` i)
            call v i = apply_delta_fill i $ g <@> v
          ty <- do
                return $ \ i -> do
                    v <- hfill lvl htype phi u u0 i
                    hd <- old_t
                    args <- delta_fill `bapp` i
                    lift $ piApplyM hd $ Arg (domInfo hdom) v : args
          ty_level <- do
            t <- bind "i" $ \ x -> ty x
            s <- reduce $ getSort (absBody t)
            reportSDoc "tc.cover.hcomp" 20 $ text "ty_level, s = " <+> prettyTCM s
            case s of
              Type l -> open =<< lam "i" (\ _ -> pure $ Level l)
              _      -> do cl <- liftTCM (buildClosure t)
                           liftTCM (cannotCreate "Cannot compose with type family:" cl)

          let
            pOr_ty i phi psi u0 u1 = pure tPOr <#> (ty_level <@> i)
                                               <@> phi <@> psi
                                               <#> ilam "o" (\ _ -> unEl <$> ty i) <@> u0 <@> u1
          alpha <- do
            vars <- mapM (open . applySubst hcompS . fst) alphab
            return $ foldr (imax . (\ v -> v `imax` ineg v)) (pure iz) vars

          -- Γ,φ,u,u0,Δ(x = hcomp φ u u0) ⊢ b : (i : I) → [α] -> old_t[x = hfill φ u u0 i,δ_fill[i]]
          b <- do
             sides <- forM alphab $ \ (psi,(side0,side1)) -> do
                psi <- open $ hcompS `applySubst` psi

                [side0,side1] <- mapM (open . raise (3+size delta) . abstract hdelta) [side0,side1]
                return $ (ineg psi `imax` psi, \ i -> pOr_ty i (ineg psi) psi (ilam "o" $ \ _ -> apply_delta_fill i $ side0 <@> hfill lvl htype phi u u0 i)
                                                            (ilam "o" $ \ _ -> apply_delta_fill i $ side1 <@> hfill lvl htype phi u u0 i))
             let recurse []           i = __IMPOSSIBLE__
                 recurse [(psi,u)]    i = u i
                 recurse ((psi,u):xs) i = pOr_ty i psi (foldr (imax . fst) (pure iz) xs) (u i) (recurse xs i)
             return $ recurse sides

          ((,) <$> ty (pure io) <*>) $ do
            comp ty_level
               (lam "i" $ fmap unEl . ty)
                           (phi `imax` alpha)
                           (lam "i" $ \ i ->
                               let rhs = (ilam "o" $ \ o -> call (u <@> i <..> o) i)
                               in if null alphab then rhs else
                                   pOr_ty i phi alpha rhs (b i)
                           )
                           (call u0 (pure iz))
    reportSDoc "tc.cover.hcomp" 20 $ text "old_tel =" <+> prettyTCM tel
    let n = size tel - (size gamma + 3 + size delta)
    reportSDoc "tc.cover.hcomp" 20 $ text "n =" <+> text (show n)
    (TelV deltaEx t,bs) <- telViewUpToPathBoundary' n ty
    rhs <- pure $ raise n rhs `applyE` teleElims deltaEx bs

    cxt <- getContextTelescope
    reportSDoc "tc.cover.hcomp" 30 $ text "cxt = " <+> prettyTCM cxt
    reportSDoc "tc.cover.hcomp" 30 $ text "tel = " <+> prettyTCM tel
    reportSDoc "tc.cover.hcomp" 20 $ addContext tel $ text "t = " <+> prettyTCM t
    reportSDoc "tc.cover.hcomp" 20 $ addContext tel $ text "rhs = " <+> prettyTCM rhs

    return $ Clause { clauseLHSRange  = noRange
                    , clauseFullRange = noRange
                    , clauseTel       = tel
                    , namedClausePats = fromSplitPatterns ps
                    , clauseBody      = Just $ rhs
                    , clauseType      = Just $ defaultArg t
                    , clauseCatchall    = False
                    , clauseExact       = Just True
                    , clauseRecursive   = Nothing     -- TODO: can it be recursive?
                    , clauseUnreachable = Just False  -- missing, thus, not unreachable
                    , clauseEllipsis    = NoEllipsis
                    , clauseWhereModule = Nothing
                    }
  addClauses f [cl]  -- Important: add at the end.
  let result = CoverResult
          { coverSplitTree      = SplittingDone (size (clauseTel cl))
          , coverUsedClauses    = IntSet.singleton (length cs)
          , coverMissingClauses = []
          , coverPatterns       = [cl]
          , coverNoExactClauses = IntSet.empty
          }
  hcompName <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinHComp
  return ([(SplitCon hcompName,result)],cs++[cl])
createMissingHCompClause _ _ _ _ (SClause _ _ _ _ Nothing) _ = __IMPOSSIBLE__
