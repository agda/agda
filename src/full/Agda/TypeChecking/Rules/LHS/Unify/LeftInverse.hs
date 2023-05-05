{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.Rules.LHS.Unify.LeftInverse where

import Prelude hiding ((!!), null)

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer (WriterT(..), MonadWriter(..))
import Control.Monad.Except

import Data.Semigroup hiding (Arg)
import qualified Data.List as List
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import qualified Agda.Benchmarking as Bench

import Agda.Interaction.Options (optInjectiveTypeConstructors, optCubical, optWithoutK)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Builtin -- (constructorForm, getTerm, builtinPathP)
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Names
import Agda.TypeChecking.Conversion -- equalTerm
import Agda.TypeChecking.Conversion.Pure
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import qualified Agda.TypeChecking.Patterns.Match as Match
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Precompute
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Records

import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Unify.Types

import Agda.Utils.Empty
import Agda.Utils.Benchmark
import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.Permutation
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.WithDefault
import Agda.Utils.Tuple

import Agda.Utils.Impossible

instance PrettyTCM NoLeftInv where
  prettyTCM (UnsupportedYet s) = fsep $ pwords "It relies on" ++ [explainStep s <> ","] ++ pwords "which is not yet supported"
  prettyTCM UnsupportedCxt     = fwords "it relies on higher-dimensional unification, which is not yet supported"
  prettyTCM (Illegal s)        = fsep $ pwords "It relies on" ++ [explainStep s <> ","] ++ pwords "which is incompatible with" ++ [text "Cubical Agda"]
  prettyTCM NoCubical          = fwords "Cubical Agda is disabled"
  prettyTCM WithKEnabled       = fwords "The K rule is enabled"
  prettyTCM SplitOnStrict      = fwords "It splits on a type in SSet"
  prettyTCM SplitOnFlat        = fwords "It splits on a @♭ argument"

data NoLeftInv
  = UnsupportedYet {badStep :: UnifyStep}
  | Illegal        {badStep :: UnifyStep}
  | NoCubical
  | WithKEnabled
  | SplitOnStrict  -- ^ splitting on a Strict Set.
  | SplitOnFlat    -- ^ splitting on a @♭ argument
  | UnsupportedCxt
  deriving Show

buildLeftInverse :: (PureTCM tcm, MonadError TCErr tcm) => UnifyState -> UnifyLog -> tcm (Either NoLeftInv (Substitution, Substitution))
buildLeftInverse s0 log = do
  reportSDoc "tc.lhs.unify.inv.badstep" 20 $ do
    cubical <- optCubical <$> pragmaOptions
    "cubical:" <+> text (show cubical)
  reportSDoc "tc.lhs.unify.inv.badstep" 20 $ do
    pathp <- getTerm' builtinPathP
    "pathp:" <+> text (show $ isJust pathp)
  let cond = andM
       -- TODO: handle open contexts: they happen during "higher dimensional" unification,
       --       in injectivity cases.
       [
         null <$> getContext
       ]
  ifNotM cond (return $ Left UnsupportedCxt) $ do
  equivs <- forM log $ uncurry buildEquiv
  case sequence equivs of
    Left no -> do
      reportSDoc "tc.lhs.unify.inv.badstep" 20 $ "No Left Inverse:" <+> prettyTCM (badStep no)
      return (Left no)
    Right xs -> do
    -- Γ,φ,us =_Δ vs ⊢ τ0 : Γ', φ
    -- Γ,φ,us =_Δ vs, i : I ⊢ leftInv0 : Γ,φ,us =_Δ vs
    -- leftInv0 : [wkS |φ,us =_Δ vs| ρ,φ,refls][τ0] = IdS : Γ,φ,us =_Δ vs
    (tau0,leftInv0) <- case xs of
      [] -> return (idS,raiseS 1)
      xs -> do
        let
            loop [] = __IMPOSSIBLE__
            loop [x] = return $ fst x
            loop (x:xs) = do
              r <- loop xs
              uncurry composeRetract x r
        (_,_,tau,leftInv) <- loop xs
        return (tau,leftInv)
    -- Γ,φ,us =_Δ vs ⊢ τ0 : Γ', φ
    -- leftInv0 : [wkS |φ,us =_Δ vs| ρ,1,refls][τ] = idS : Γ,φ,us =_Δ vs
    let tau = tau0 `composeS` raiseS 1
    unview <- intervalUnview'
    let replaceAt n x xs = xs0 ++ x:xs1
                where (xs0,_:xs1) = splitAt n xs
    let max r s = unview $ IMax (argN r) (argN s)
        neg r = unview $ INeg (argN r)
    let phieq = neg (var 0) `max` var (size (eqTel s0) + 1)
                       -- I + us =_Δ vs -- inplaceS
    let leftInv = termsS __IMPOSSIBLE__ $ replaceAt (size (varTel s0)) phieq $ map (lookupS leftInv0) $ downFrom (size (varTel s0) + 1 + size (eqTel s0))
    let working_tel = abstract (varTel s0) (ExtendTel __DUMMY_DOM__ $ Abs "phi0" $ (eqTel s0))
    reportSDoc "tc.lhs.unify.inv" 20 $ "=== before mod"
    do
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau0    :" <+> prettyTCM tau0
        addContext working_tel $ addContext ("r" :: String, __DUMMY_DOM__)
                               $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv0:  " <+> prettyTCM leftInv0

    reportSDoc "tc.lhs.unify.inv" 20 $ "=== after mod"
    do
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau    :" <+> prettyTCM tau
        addContext working_tel $ addContext ("r" :: String, __DUMMY_DOM__)
                               $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv:   " <+> prettyTCM leftInv

    return $ Right (tau,leftInv)

type Retract = (Telescope, Substitution, Substitution, Substitution)
     -- Γ (the problem, including equalities),
     -- Δ ⊢ ρ : Γ
     -- Γ ⊢ τ : Δ
     -- Γ, i : I ⊢ leftInv : Γ, such that (λi. leftInv) : ρ[τ] = id_Γ

--- Γ ⊢ us : Δ   Γ ⊢ termsS e us : Δ
termsS ::  DeBruijn a => Impossible -> [a] -> Substitution' a
termsS e xs = reverse xs ++# EmptyS e

composeRetract :: (PureTCM tcm, MonadError TCErr tcm, MonadDebug tcm,HasBuiltins tcm, MonadAddContext tcm) => Retract -> Term -> Retract -> tcm Retract
composeRetract (prob0,rho0,tau0,leftInv0) phi0 (prob1,rho1,tau1,leftInv1) = do
  reportSDoc "tc.lhs.unify.inv" 20 $ "=== composing"
  reportSDoc "tc.lhs.unify.inv" 20 $ "Γ0   :" <+> prettyTCM prob0
  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau0  :" <+> prettyTCM tau0
  reportSDoc "tc.lhs.unify.inv" 20 $ "Γ1   :" <+> prettyTCM prob1
  addContext prob1 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau1  :" <+> prettyTCM tau1


  {-
  Γ0 = prob0
  S0 ⊢ ρ0 : Γ0
  Γ0 ⊢ τ0 : S0
  Γ0 ⊢ leftInv0 : ρ0[τ0] = idΓ0
  Γ0 ⊢ φ0
  Γ0,φ0 ⊢ leftInv0 = refl

  Γ1 = prob1
  S1 ⊢ ρ1 : Γ1
  Γ1 ⊢ τ1 : S1
  Γ1 ⊢ leftInv1 : ρ1[τ1] = idΓ1
  Γ1 ⊢ φ1 = φ0[τ0] (**)
  Γ1,φ1 ⊢ leftInv1 = refl
  S0 = Γ1

  (**) implies?
  Γ0,φ0 ⊢ leftInv1[τ0] = refl  (*)


  S1 ⊢ ρ := ρ0[ρ1] : Γ0
  Γ0 ⊢ τ := τ1[τ0] : S1
  -}

  let prob = prob0
  let rho = rho1 `composeS` rho0
  let tau = tau0 `composeS` tau1

  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau  :" <+> prettyTCM tau

  {-
  Γ0 ⊢ leftInv : ρ[τ] = idΓ0
  Γ0 ⊢ leftInv : ρ0[ρ1[τ1]][τ0] = idΓ0
  Γ0 ⊢ step0 := ρ0[leftInv1[τ0]] : ρ0[ρ1[τ1]][τ0] = ρ0[τ0]

  Γ0,φ0 ⊢ step0 = refl     by (*)


  Γ0 ⊢ leftInv := step0 · leftInv0 : ρ0[ρ1[τ1]][τ0] = idΓ0

  Γ0 ⊢ leftInv := tr (\ i → ρ0[ρ1[τ1]][τ0] = leftInv0[i]) φ0 step0
  Γ0,φ0 ⊢ leftInv = refl  -- because it will become step0, which is refl when φ0

  Γ0, i : I ⊢ hcomp {Γ0} (\ j → \ { (i = 0) -> ρ0[ρ1[τ1]][τ0]
                                  ; (i = 1) -> leftInv0[j]
                                  ; (φ0 = 1) -> γ0
                                  })
                         (step0[i])




  -}
  let step0 = liftS 1 tau0 `composeS` leftInv1 `composeS` rho0

  addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv0  :" <+> prettyTCM leftInv0
  addContext prob1 $ reportSDoc "tc.lhs.unify.inv" 20 $ "rho0  :" <+> prettyTCM rho0
  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau0  :" <+> prettyTCM tau0
  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "rhos0[tau0]  :" <+> prettyTCM (tau0 `composeS` rho0)

  addContext prob1 $ addContext ("r" :: String, __DUMMY_DOM__) $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv1  :" <+> prettyTCM leftInv1
  addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) $ reportSDoc "tc.lhs.unify.inv" 20 $ "step0  :" <+> prettyTCM step0

  interval <- primIntervalType
  max <- primIMax
  neg <- primINeg
  Right leftInv <- fmap sequenceA $ addContext prob0 $ runNamesT (teleNames prob0) $ do
             phi <- open phi0
             g0 <- open $ raise (size prob0) prob0
             step0 <- open $ Abs "i" $ step0 `applySubst` teleArgs prob0
             leftInv0 <- open $ Abs "i" $ map unArg $ leftInv0 `applySubst` teleArgs prob0
             bind "i" $ \ i -> addContext ("i" :: String, defaultDom interval) $ do
              tel <- bind "_" $ \ (_ :: NamesT tcm Term) -> g0
              step0i <- lazyAbsApp <$> step0 <*> i
              face <- pure max <@> (pure neg <@> i) <@> phi
              leftInv0 <- leftInv0
              i <- i
              -- this composition could be optimized further whenever step0i is actually constant in i.
              lift $ (runExceptT $ map unArg <$> transpSysTel' True tel [(i, leftInv0)] face step0i)
  addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) $
    reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv  :" <+> prettyTCM (absBody leftInv)
  addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) $
    reportSDoc "tc.lhs.unify.inv" 40 $ "leftInv  :" <+> pretty (absBody leftInv)
  addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) $
    reportSDoc "tc.lhs.unify.inv" 40 $ "leftInvSub  :" <+> pretty (termsS __IMPOSSIBLE__ $ absBody $ leftInv)
  return (prob, rho, tau , termsS __IMPOSSIBLE__ $ absBody $ leftInv)

buildEquiv :: forall tcm. (PureTCM tcm, MonadError TCErr tcm) => UnifyLogEntry -> UnifyState -> tcm (Either NoLeftInv (Retract,Term))
buildEquiv (UnificationStep st step@(Solution k ty fx tm side) output) next = runExceptT $ do
        let
          errorToUnsupported :: ExceptT a tcm b -> ExceptT NoLeftInv tcm b
          errorToUnsupported m = withExceptT (\ _ -> UnsupportedYet step) m
        reportSDoc "tc.lhs.unify.inv" 20 $ "step unifyState:" <+> prettyTCM st
        reportSDoc "tc.lhs.unify.inv" 20 $ "step step:" <+> addContext (varTel st) (prettyTCM step)
        unview <- intervalUnview'
        cxt <- getContextTelescope
        reportSDoc "tc.lhs.unify.inv" 20 $ "context:" <+> prettyTCM cxt
        let
          -- k counds in eqs from the left
          m = varCount st
          gamma = varTel st
          eqs = eqTel st
          u = eqLHS st !! k
          v = eqRHS st !! k
          x = flexVar fx
          neqs = size eqs
          phis = 1 -- neqs
        interval <- lift $ primIntervalType
         -- Γ, φs : I^phis
        let gamma_phis = abstract gamma $ telFromList $
              map (defaultDom . (,interval) . ("phi" ++) . show) [0 .. phis - 1]
        working_tel <- abstract gamma_phis <$>
          errorToUnsupported (pathTelescope' (raise phis $ eqTel st) (raise phis $ eqLHS st) (raise phis $ eqRHS st))
        reportSDoc "tc.lhs.unify.inv" 20 $ vcat
          [ "working tel:" <+> prettyTCM (working_tel :: Telescope)
          , addContext working_tel $ "working tel args:" <+> prettyTCM (teleArgs working_tel :: [Arg Term])
          ]
        (tau,leftInv,phi) <- addContext working_tel $ runNamesT [] $ do
          let raiseFrom tel x = raise (size working_tel - size tel) x

          [u,v] <- mapM (open . raiseFrom gamma . unArg) [u,v]
          -- φ
          let phi = raiseFrom gamma_phis $ var 0
          -- working_tel ⊢ γ₁,x,γ₂,φ,eqs
          let all_args = teleArgs working_tel
          -- Γ₁,x : A,Γ₂
--          gamma <- open $ raiseFrom EmptyTel gamma
          -- -- γ₁,x,γ₂,φ,eqs : W
          -- working_tel <- open $ raiseFrom EmptyTel working_tel

          -- eq_tel <- open $ raiseFrom gamma (eqTel st)

          -- [lhs,rhs] <- mapM (open . raiseFrom gamma) [eqLHS st,eqRHS st]
          let bindSplit (tel1,tel2) = (tel1,AbsN (teleNames tel1) tel2)
          -- . ⊢ Γ₁  ,  γ₁. (x : A),Γ₂,φ : I,[lhs ≡ rhs]
          let (gamma1, xxi) = bindSplit $ splitTelescopeAt (size gamma - x - 1) working_tel
          let (gamma1_args,xxi_args) = splitAt (size gamma1) all_args
              (_x_arg:xi_args) = xxi_args
              (x_arg:xi0,k_arg:xi1) = splitAt ((size gamma - size gamma1) + phis + k) xxi_args
              -- W ⊢ (x : A),Γ₂,φ : I,[lhs ≡ rhs]
          let
            xxi_here :: Telescope
            xxi_here = absAppN xxi $ map unArg gamma1_args
          --                                                      x:A,Γ₂                φ
          let (xpre,krest) = bindSplit $ splitTelescopeAt ((size gamma - size gamma1) + phis + k) xxi_here
          k_arg <- open $ unArg k_arg
          xpre <- open xpre
          krest <- open krest
          delta <- bindN ["x","eq"] $ \ [x,eq] -> do
                     let pre = apply1 <$> xpre <*> x
                     abstractN pre $ \ args ->
                       apply1 <$> applyN krest (x:args) <*> eq
--          let delta_zero = absAppN delta $ map unArg [x_arg,k_arg]
          let d_zero_args = xi0 ++ xi1
          reportSDoc "tc.lhs.unify.inv" 20 $ "size delta:" <+> text (show $ size $ unAbsN delta)
          reportSDoc "tc.lhs.unify.inv" 20 $ "size d0args:" <+> text (show $ size d_zero_args)
          let appSide = case side of
                          Left{} -> id
                          Right{} -> unview . INeg . argN
          let
                  -- csingl :: NamesT tcm Term -> NamesT tcm [Arg Term]
                  csingl i = mapM (fmap defaultArg) $ csingl' i
                  -- csingl' :: NamesT tcm Term -> [NamesT tcm Term]
                  csingl' i = [ k_arg <@@> (u, v, appSide <$> i)
                              , lam "j" $ \ j ->
                                  let r i j = case side of
                                            Left{} -> unview (IMax (argN j) (argN i))
                                            Right{} -> unview (IMin (argN j) (argN . unview $ INeg $ argN i))
                                  in k_arg <@@> (u, v, r <$> i <*> j)
                              ]
          let replaceAt n x xs = xs0 ++ x:xs1
                where (xs0,_:xs1) = splitAt n xs
              dropAt n xs = xs0 ++ xs1
                where (xs0,_:xs1) = splitAt n xs
          delta <- open delta
          d <- bind "i" $ \ i -> applyN delta (csingl' i)

          -- Andrea 06/06/2018
          -- We do not actually add a transp/fill if the family is
          -- constant (TODO: postpone for metas) This is so variables
          -- whose types do not depend on "x" are left alone, in
          -- particular those the solution "t" depends on.
          --
          -- We might want to instead use the info discovered by the
          -- solver when checking if "t" depends on "x" to decide what
          -- to transp and what not to.
          let flag = True
                 {-   φ -}
          tau <- {-dropAt (size gamma - 1 + k) .-} (gamma1_args ++) <$>
                                                   lift (errorToUnsupported (transpTel' flag d phi d_zero_args))
          reportSDoc "tc.lhs.unify.inv" 20 $ "tau    :" <+> prettyTCM (map (setHiding NotHidden) tau)
          leftInv <- do
            gamma1_args <- open gamma1_args
            phi <- open phi
            -- xxi_here <- open xxi_here
            -- (xi_here_f :: Abs Telescope) <- bind "i" $ \ i -> apply <$> xxi_here <*> (take 1 `fmap` csingl i)
            -- xi_here_f <- open xi_here_f
            -- xi_args <- open xi_args
            -- xif <- bind "i" $ \ i -> do
            --                      m <- (runExceptT <$> (trFillTel' flag <$> xi_here_f <*> phi <*> xi_args <*> i))
            --                      either __IMPOSSIBLE__ id <$> lift m
            -- xif <- open xif

            xi0 <- open xi0
            xi1 <- open xi1
            delta0 <- bind "i" $ \ i -> apply <$> xpre <*> (take 1 `fmap` csingl i)
            delta0 <- open delta0
            xi0f <- bind "i" $ \ i -> do
                                 m <- trFillTel' flag <$> delta0 <*> phi <*> xi0 <*> i
                                 lift (errorToUnsupported m)
            xi0f <- open xi0f

            delta1 <- bind "i" $ \ i -> do

                   args <- mapM (open . unArg) =<< (lazyAbsApp <$> xi0f <*> i)
                   apply <$> applyN krest ((take 1 $ csingl' i) ++ args) <*> (drop 1 `fmap` csingl i)
            delta1 <- open delta1
            xi1f <- bind "i" $ \ i -> do
                                 m <- trFillTel' flag <$> delta1 <*> phi <*> xi1 <*> i
                                 lift (errorToUnsupported m)
            xi1f <- open xi1f
            fmap absBody $ bind "i" $ \ i' -> do
              let (+++) m = liftM2 (++) m
                  i = cl (lift primINeg) <@> i'
--              replaceAt (size gamma + k) <$> (fmap defaultArg $ cl primIMax <@> phi <@> i) <*> do
              do
                gamma1_args +++ (take 1 `fmap` csingl i +++ ((lazyAbsApp <$> xi0f <*> i) +++ (drop 1 `fmap` csingl i +++ (lazyAbsApp <$> xi1f <*> i))))
          return (tau,leftInv,phi)
        iz <- lift $ primIZero
        io <- lift $ primIOne
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau    :" <+> prettyTCM (map (setHiding NotHidden) tau)
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tauS   :" <+> prettyTCM (termsS __IMPOSSIBLE__ $ map unArg tau)
        addContext working_tel $ addContext ("r" :: String, defaultDom interval)
                               $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv:   " <+> prettyTCM (map (setHiding NotHidden) leftInv)
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv[0]:" <+> (prettyTCM =<< reduce (subst 0 iz $ map (setHiding NotHidden) leftInv))
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv[1]:" <+> (prettyTCM =<< reduce  (subst 0 io $ map (setHiding NotHidden) leftInv))
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "[rho]tau :" <+>
                                                                                  -- k   φ
          prettyTCM (applySubst (termsS __IMPOSSIBLE__ $ map unArg tau) $ fromPatternSubstitution
                                                                      $ raise (size (eqTel st) - 1{-k-} + phis {-neqs{-φs-} - 1{-φ0-}-})
                                                                      $ unifySubst output)
        reportSDoc "tc.lhs.unify.inv" 20 $ "."
        let rho0 = fromPatternSubstitution $ unifySubst output
        addContext (varTel next) $ addContext (eqTel next) $ reportSDoc "tc.lhs.unify.inv" 20 $
          "prf :" <+> prettyTCM (fromPatternSubstitution $ unifyProof output)
        let c0 = Lam defaultArgInfo $ Abs "i" $ raise 1 $ lookupS (fromPatternSubstitution $ unifyProof output) (neqs - k - 1)
        let c = liftS (size $ eqTel next) (raiseS 1) `applySubst` c0
        addContext (varTel next) $ addContext ("φ" :: String, __DUMMY_DOM__) $ addContext (raise 1 $ eqTel next) $
          reportSDoc "tc.lhs.unify.inv" 20 $ "c :" <+> prettyTCM c
--        let rho = liftS (neqs - k - 1) $ consS (raise (1 + k) c) $ liftS (1 + k) rho0
        let rho = singletonS (neqs - k - 1) c  `composeS` liftS (1 + neqs) rho0
        reportSDoc "tc.lhs.unify.inv" 20 $ text "old_sizes: " <+> pretty (size $ varTel st, size $ eqTel st)
        reportSDoc "tc.lhs.unify.inv" 20 $ text "new_sizes: " <+> pretty (size $ varTel next, size $ eqTel next)
--        addContext (abstract (varTel next) $ ExtendTel __DUMMY_DOM__ (Abs "φ" $ raise 1 $ eqTel next)) $
        addContext (varTel next) $ addContext ("φ" :: String, __DUMMY_DOM__) $ addContext (raise 1 $ eqTel next) $
          reportSDoc "tc.lhs.unify.inv" 20 $ "rho   :" <+> prettyTCM rho
        return $ ((working_tel
                 , rho
                 , termsS __IMPOSSIBLE__ $ map unArg tau
                 , termsS __IMPOSSIBLE__ $ map unArg leftInv)
                 , phi)
buildEquiv (UnificationStep st step@(EtaExpandVar fv _d _args) output) next = fmap Right $ do
        reportSDoc "tc.lhs.unify.inv" 20 "buildEquiv EtaExpandVar"
        let
          gamma = varTel st
          eqs = eqTel st
          x = flexVar fv
          neqs = size eqs
          phis = 1
        interval <- primIntervalType
         -- Γ, φs : I^phis
        let gamma_phis = abstract gamma $ telFromList $
              map (defaultDom . (,interval) . ("phi"++) . show) [0 .. phis - 1]
        working_tel <- abstract gamma_phis <$>
          pathTelescope (raise phis $ eqTel st) (raise phis $ eqLHS st) (raise phis $ eqRHS st)
        let raiseFrom tel x = (size working_tel - size tel) + x
        let phi = var $ raiseFrom gamma_phis 0

        caseMaybeM (expandRecordVar (raiseFrom gamma x) working_tel) __IMPOSSIBLE__ $ \ (_,tau,rho,_) -> do
          reportSDoc "tc.lhs.unify.inv" 20 $ addContext working_tel $ "tau    :" <+> prettyTCM tau
          return $ ((working_tel,rho,tau,raiseS 1),phi)

buildEquiv (UnificationStep st step output) _ = do
  reportSDoc "tc.lhs.unify.inv" 20 $ "steps"
  let illegal     = return $ Left $ Illegal step
      unsupported = return $ Left $ UnsupportedYet step
  case step of
    Deletion{}           -> illegal
    TypeConInjectivity{} -> illegal
    -- These should end up in a NoUnify
    Conflict{}    -> __IMPOSSIBLE__
    LitConflict{} -> __IMPOSSIBLE__
    Cycle{}       -> __IMPOSSIBLE__
    _ -> unsupported

explainStep :: MonadPretty m => UnifyStep -> m Doc
explainStep Injectivity{injectConstructor = ch} =
  "injectivity of the data constructor" <+> prettyTCM (conName ch)
explainStep TypeConInjectivity{} = "injectivity of type constructors"
explainStep Deletion{}           = "the K rule"
explainStep Solution{}           = "substitution in Setω"
-- Note: this is the actual reason that a Solution step can fail, rather
-- than the explanation for the actual step
explainStep Conflict{}          = "the disjointness of data constructors"
explainStep LitConflict{}       = "the disjointness of literal values"
explainStep Cycle{}             = "the impossibility of cyclic values"
explainStep EtaExpandVar{}      = "eta-expansion of variables"
explainStep EtaExpandEquation{} = "eta-expansion of equations"
explainStep StripSizeSuc{}      = "the injectivity of size successors"
explainStep SkipIrrelevantEquation{} = "ignoring irrelevant equations"
