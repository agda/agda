{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Constraints where

import Prelude hiding (null)

import Control.Applicative hiding (empty)

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.List as List hiding (null)

import Agda.Syntax.Internal

import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.LevelConstraints
import Agda.TypeChecking.SizedTypes

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Empty

import Agda.Utils.Except ( MonadError(throwError) )
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Lens
import Agda.Utils.Size
import qualified Agda.Utils.VarSet as VarSet

#include "undefined.h"
import Agda.Utils.Impossible

-- | Catches pattern violation errors and adds a constraint.
--
catchConstraint :: Constraint -> TCM () -> TCM ()
catchConstraint c v = liftTCM $
   catchError_ v $ \err ->
   case err of
        -- Not putting s (which should really be the what's already there) makes things go
        -- a lot slower (+20% total time on standard library). How is that possible??
        -- The problem is most likely that there are internal catchErrors which forgets the
        -- state. catchError should preserve the state on pattern violations.
       PatternErr{} -> addConstraint c
       _            -> throwError err

addConstraint :: Constraint -> TCM ()
addConstraint c = do
    pids <- asks envActiveProblems
    reportSDoc "tc.constr.add" 20 $ hsep
      [ text "adding constraint"
      , text (show pids)
      , prettyTCM c ]
    -- Need to reduce to reveal possibly blocking metas
    c <- reduce =<< instantiateFull c
    c' <- simpl c
    if (c /= c')
      then do
        reportSDoc "tc.constr.add" 20 $ text "  simplified:" <+> prettyTCM c'
        solveConstraint_ c'
      else addConstraint' c'
    -- the added constraint can cause IFS constraints to be solved (but only
    -- the constraints which aren’t blocked on an uninstantiated meta)
    unless (isIFSConstraint c) $
       wakeConstraints (isWakeableIFSConstraint . clValue . theConstraint)
  where
    isWakeableIFSConstraint :: Constraint -> TCM Bool
    isWakeableIFSConstraint (FindInScope _ b _) = caseMaybe b (return True) (\m -> isInstantiatedMeta m)
    isWakeableIFSConstraint _ = return False

    isIFSConstraint :: Constraint -> Bool
    isIFSConstraint FindInScope{} = True
    isIFSConstraint _             = False

    isLvl LevelCmp{} = True
    isLvl _          = False

    -- Try to simplify a level constraint
    simpl :: Constraint -> TCM Constraint
    simpl c = if not $ isLvl c then return c else do
      n <- genericLength <$> getContext
      cs <- map theConstraint <$> getAllConstraints
      lvls <- instantiateFull $ List.filter (isLvl . clValue) cs
      when (not $ null lvls) $ do
        reportSDoc "tc.constr.lvl" 40 $ text "  simplifying using" <+> prettyTCM lvls
        reportSDoc "tc.constr.lvl" 80 $ do
          cxt <- getContextTelescope
          inTopContext $ do
            text "simpl" <+> do
              vcat $
                [ text "current module  = " <+> (prettyTCM =<< currentModule)
                , text "current context = " <+> prettyTCM cxt
                , text "current m.pars  = " <+> (prettyTCM =<< use stModuleParameters)
                , text "constraints: "
                ] ++ do
                  for lvls $ \ cl -> do
                    let cxt' = envContext (clEnv cl)
                        mp   = clModuleParameters cl
                    vcat
                      [ text "*" <+> text "module = " <+> prettyTCM (envCurrentModule $ clEnv cl)
                      , nest 2 $ text "m.pars = " <+> prettyTCM mp
                      , nest 2 $ hang (prettyTCM cxt' <+> text "|-") 2 (prettyTCM cl)
                      ]
      simplifyLevelConstraint c . catMaybes <$>
        mapM (runMaybeT . castConstraintToCurrentContext) lvls

-- | We would like to use a constraint @c@ created in context @Δ@ from module @N@
--   in the current context @Γ@ and current module @M@.
--
--   @Δ@ is module tel @Δ₁@ of @N@ extended by some local bindings @Δ₂@.
--   @Γ@ is the current context.
--   The module parameter substitution from current @M@ to @N@ be
--   @Γ ⊢ σ : Δ₁@.
--
--   If @M == N@, we do not need the parameter substitution.  We try raising.
--
--   We first strengthen @Δ ⊢ c@ to live in @Δ₁@ and obtain @c₁ = strengthen Δ₂ c@.
--   We then transport @c₁@ to @Γ@ and obtain @c₂ = applySubst σ c₁@.
--
--   This works for different modules, but if @M == N@ we should not strengthen
--   and then weaken, because strengthening is a partial operation.
--   We should rather lift the substitution @σ@ by @Δ₂@ and then
--   raise by @Γ₂ - Δ₂@.
--   This "raising" might be a strengthening if @Γ₂@ is shorter than @Δ₂@.
--
--   (TODO: If the module substitution does not exist, because @N@ is not
--   a parent of @M@, we cannot use the constraint, as it has been created
--   in an unrelated context.)

castConstraintToCurrentContext :: Closure Constraint -> MaybeT TCM Constraint
castConstraintToCurrentContext cl = do
  let modN  = envCurrentModule $ clEnv cl
      delta = envContext $ clEnv cl
  -- The module telescope of the constraint.
  -- The constraint could come from the module telescope of the top level module.
  -- In this case, it does not live in any module!
  -- Thus, getSection can return Nothing.
  delta1 <- liftTCM $ maybe empty (^. secTelescope) <$> getSection modN
  -- The number of locals of the constraint.
  let delta2 = size delta - size delta1
  unless (delta2 >= 0) __IMPOSSIBLE__

  -- The current module M and context Γ.
  modM  <- currentModule
  gamma <- liftTCM $ getContextSize
  -- The current module telescope.
  -- Could also be empty, if we are in the front matter or telescope of the top-level module.
  gamma1 <-liftTCM $ maybe empty (^. secTelescope) <$> getSection modM
  -- The current locals.
  let gamma2 = gamma - size gamma1

  -- If gamma2 < 0, we must be in the wrong context.
  -- E.g. we could have switched to the empty context even though
  -- we are still inside a module with parameters.
  -- In this case, we cannot safely convert the constraint,
  -- since the module parameter substitution may be wrong.
  guard (gamma2 >= 0)

  -- Shortcut for modN == modM:
  -- Raise constraint from Δ to Γ, if possible.
  -- This might save us some strengthening.
  if modN == modM then raiseMaybe (gamma - size delta) $ clValue cl else do

  -- Strengthen constraint to Δ₁ ⊢ c
  c <- raiseMaybe (-delta2) $ clValue cl
  -- Γ ⊢ σ : Δ₁
  sigma <- liftTCM $ getModuleParameterSub modN
  -- Γ ⊢ c[σ]

  -- Ulf, 2016-11-09: I don't understand what this function does when M and N
  -- are not related. Certainly things can go terribly wrong (see
  -- test/Succeed/Issue2223b.agda)
  fv <- liftTCM $ getModuleFreeVars modN
  guard $ fv == size delta1

  return $ applySubst sigma c
  where
    raiseMaybe n c = do
      -- Fine if we have to weaken or strengthening is safe.
      guard $ n >= 0 || List.all (>= -n) (VarSet.toList $ allVars $ freeVars c)
      return $ raise n c

-- | Don't allow the argument to produce any constraints.
noConstraints :: TCM a -> TCM a
noConstraints problem = liftTCM $ do
  (pid, x) <- newProblem problem
  cs <- getConstraintsForProblem pid
  w <- warning_ (UnsolvedConstraints cs)
  unless (null cs) $ typeError $ NonFatalErrors [ w ]
  return x

-- | Create a fresh problem for the given action.
newProblem :: TCM a -> TCM (ProblemId, a)
newProblem action = do
  pid <- fresh
  -- Don't get distracted by other constraints while working on the problem
  x <- nowSolvingConstraints $ solvingProblem pid action
  -- Now we can check any woken constraints
  solveAwakeConstraints
  return (pid, x)

newProblem_ :: TCM () -> TCM ProblemId
newProblem_ action = fst <$> newProblem action

ifNoConstraints :: TCM a -> (a -> TCM b) -> (ProblemId -> a -> TCM b) -> TCM b
ifNoConstraints check ifNo ifCs = do
  (pid, x) <- newProblem check
  ifM (isProblemSolved pid) (ifNo x) (ifCs pid x)

ifNoConstraints_ :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
ifNoConstraints_ check ifNo ifCs = ifNoConstraints check (const ifNo) (\pid _ -> ifCs pid)

-- | @guardConstraint c blocker@ tries to solve @blocker@ first.
--   If successful without constraints, it moves on to solve @c@, otherwise it
--   adds a @Guarded c cs@ constraint
--   to the @blocker@-generated constraints @cs@.
guardConstraint :: Constraint -> TCM () -> TCM ()
guardConstraint c blocker =
  ifNoConstraints_ blocker (solveConstraint_ c) (addConstraint . Guarded c)

whenConstraints :: TCM () -> TCM () -> TCM ()
whenConstraints action handler =
  ifNoConstraints_ action (return ()) $ \pid -> do
    stealConstraints pid
    handler

-- | Wake up the constraints depending on the given meta.
wakeupConstraints :: MetaId -> TCM ()
wakeupConstraints x = do
  wakeConstraints (return . const True) -- (mentionsMeta x) -- TODO: needs fixing to cope with shared updates
  solveAwakeConstraints

-- | Wake up all constraints.
wakeupConstraints_ :: TCM ()
wakeupConstraints_ = do
  wakeConstraints (return . const True)
  solveAwakeConstraints

solveAwakeConstraints :: TCM ()
solveAwakeConstraints = solveAwakeConstraints' False

solveAwakeConstraints' :: Bool -> TCM ()
solveAwakeConstraints' force = do
    verboseS "profile.constraints" 10 $ liftTCM $ tickMax "max-open-constraints" . genericLength =<< getAllConstraints
    whenM ((force ||) . not <$> isSolvingConstraints) $ nowSolvingConstraints $ do
     -- solveSizeConstraints -- Andreas, 2012-09-27 attacks size constrs too early
     solve
  where
    solve = do
      reportSDoc "tc.constr.solve" 10 $ hsep [ text "Solving awake constraints."
                                             , text . show . length =<< getAwakeConstraints
                                             , text "remaining." ]
      whenJustM takeAwakeConstraint $ \ c -> do
        withConstraint solveConstraint c
        solve

solveConstraint :: Constraint -> TCM ()
solveConstraint c = do
    verboseS "profile.constraints" 10 $ liftTCM $ tick "attempted-constraints"
    verboseBracket "tc.constr.solve" 20 "solving constraint" $ do
      pids <- asks envActiveProblems
      reportSDoc "tc.constr.solve" 20 $ text (show pids) <+> prettyTCM c
      solveConstraint_ c

solveConstraint_ :: Constraint -> TCM ()
solveConstraint_ (ValueCmp cmp a u v)       = compareTerm cmp a u v
solveConstraint_ (ElimCmp cmp a e u v)      = compareElims cmp a e u v
solveConstraint_ (TypeCmp cmp a b)          = compareType cmp a b
solveConstraint_ (TelCmp a b cmp tela telb) = compareTel a b cmp tela telb
solveConstraint_ (SortCmp cmp s1 s2)        = compareSort cmp s1 s2
solveConstraint_ (LevelCmp cmp a b)         = compareLevel cmp a b
solveConstraint_ c0@(Guarded c pid)         = do
  ifM (isProblemSolved pid) (solveConstraint_ c)
                            (addConstraint c0)
solveConstraint_ (IsEmpty r t)              = isEmptyType r t
solveConstraint_ (CheckSizeLtSat t)         = checkSizeLtSat t
solveConstraint_ (UnBlock m)                =
  ifM (isFrozen m) (addConstraint $ UnBlock m) $ do
    inst <- mvInstantiation <$> lookupMeta m
    reportSDoc "tc.constr.unblock" 15 $ text ("unblocking a metavar yields the constraint: " ++ show inst)
    case inst of
      BlockedConst t -> do
        reportSDoc "tc.constr.blocked" 15 $
          text ("blocked const " ++ prettyShow m ++ " :=") <+> prettyTCM t
        assignTerm m [] t
      PostponedTypeCheckingProblem cl unblock -> enterClosure cl $ \prob -> do
        ifNotM unblock (addConstraint $ UnBlock m) $ do
          tel <- getContextTelescope
          v   <- liftTCM $ checkTypeCheckingProblem prob
          assignTerm m (telToArgs tel) v
      -- Andreas, 2009-02-09, the following were IMPOSSIBLE cases
      -- somehow they pop up in the context of sized types
      --
      -- already solved metavariables: should only happen for size
      -- metas (not sure why it does, Andreas?)
      InstV{} -> return ()
      -- Open (whatever that means)
      Open -> __IMPOSSIBLE__
      OpenIFS -> __IMPOSSIBLE__
solveConstraint_ (FindInScope m b cands)      = findInScope m cands

checkTypeCheckingProblem :: TypeCheckingProblem -> TCM Term
checkTypeCheckingProblem p = case p of
  CheckExpr e t                  -> checkExpr e t
  CheckArgs eh r args t0 t1 k    -> checkArguments' eh r args t0 t1 k
  CheckLambda args body target   -> checkPostponedLambda args body target
  UnquoteTactic tac hole t       -> unquoteTactic tac hole t $ return hole

debugConstraints :: TCM ()
debugConstraints = verboseS "tc.constr" 50 $ do
  awake    <- use stAwakeConstraints
  sleeping <- use stSleepingConstraints
  reportSDoc "" 0 $ vcat
    [ text "Current constraints"
    , nest 2 $ vcat [ text "awake " <+> vcat (map prettyTCM awake)
                    , text "asleep" <+> vcat (map prettyTCM sleeping) ] ]
