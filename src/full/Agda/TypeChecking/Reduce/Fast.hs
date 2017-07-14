{-# LANGUAGE CPP           #-}
{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE PatternGuards #-}


{-|

This module contains an optimised implementation of the reduction algorithm
from 'Agda.TypeChecking.Reduce' and 'Agda.TypeChecking.CompiledClause.Match'.
It runs roughly an order of magnitude faster than the original implementation.

The differences are the following:

- Only applies when we don't have --sharing and when all reductions are
  allowed.

  This means we can skip a number of checks that would otherwise be performed
  at each reduction step.

- Does not track whether simplifications were made.

  This information is only used when trying to simplify terms, so the
  simplifier runs the slow implementation.

- Precomputes primZero and primSuc.

  Since all the functions involved in reduction are implemented in this module
  in a single where block, we can look up zero and suc once instead of once for
  each reduction step.

- Run outside ReduceM

  ReduceM is already just a plain reader monad, but pulling out the environment
  and doing all reduction non-monadically saves a significant amount of time.

- Memoise getConstInfo.

  A big chunk of the time during reduction is spent looking up definitions in
  the signature. Any long-running reduction will use only a handful definitions
  though, so memoising getConstInfo is a big win.

- Optimised case trees.

  Since we memoise getConstInfo we can do some preprocessing of the
  definitions, returning a 'CompactDef' instead of a 'Definition'. In
  particular we streamline the case trees used for matching in a few ways:

    - Drop constructor arity information.
    - Use NameId instead of QName as map keys.
    - Special branch for natural number successor.

  None of these changes would make sense to incorporate into the actual case
  trees. The first two loses information that we need in other places and the
  third would complicate a lot of code working with case trees.

- Optimised parallel substitution.

  When substituting arguments into function bodies we always have a complete
  (a term for every free variable) parallel substitution. We run an specialised
  substitution for this case that falls back to normal substitution when it
  hits a binder.

-}
module Agda.TypeChecking.Reduce.Fast
  ( fastReduce ) where

import Control.Applicative
import Control.Monad.Reader

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (traverse)

import System.IO.Unsafe
import Data.IORef

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce as R
import Agda.TypeChecking.Rewriting (rewrite)
import Agda.TypeChecking.Reduce.Monad as RedM
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Builtin hiding (constructorForm)
import Agda.TypeChecking.CompiledClause.Match

import Agda.Interaction.Options

import Agda.Utils.Maybe
import Agda.Utils.Memo
import Agda.Utils.Function
import Agda.Utils.Functor

#include "undefined.h"
import Agda.Utils.Impossible

-- Compact definitions ----------------------------------------------------

-- This is what the memoised getConstInfo returns. We essentially pick out only the
-- information needed for fast reduction from the definition.

data CompactDef =
  CompactDef { cdefDelayed        :: Bool
             , cdefNonterminating :: Bool
             , cdefDef            :: CompactDefn
             , cdefRewriteRules   :: RewriteRules
             }

data CompactDefn
  = CFun  { cfunCompiled  :: FastCompiledClauses, cfunProjection :: Maybe QName }
  | CCon  { cconSrcCon    :: ConHead }
  | CForce  -- ^ primForce
  | CTyCon  -- ^ Datatype or record type. Need to know this for primForce.
  | COther  -- ^ In this case we fall back to slow reduction

compactDef :: Maybe ConHead -> Maybe ConHead -> Maybe QName -> Definition -> RewriteRules -> ReduceM CompactDef
compactDef z s pf def rewr = do
  cdefn <-
    case theDef def of
      _ | Just (defName def) == pf -> pure CForce
      Constructor{conSrcCon = c} -> pure CCon{cconSrcCon = c}
      Function{funCompiled = Just cc, funClauses = _:_, funProjection = proj} ->
        pure CFun{ cfunCompiled   = fastCompiledClauses z s cc
                 , cfunProjection = projOrig <$> proj }
      Datatype{dataClause = Nothing} -> pure CTyCon
      Record{recClause = Nothing} -> pure CTyCon
      _ -> pure COther
  return $
    CompactDef { cdefDelayed        = defDelayed def == Delayed
               , cdefNonterminating = defNonterminating def
               , cdefDef            = cdefn
               , cdefRewriteRules   = rewr
               }

-- Faster case trees ------------------------------------------------------

data FastCase c = FBranches
  { fprojPatterns   :: Bool
    -- ^ We are constructing a record here (copatterns).
    --   'conBranches' lists projections.
  , fconBranches    :: Map NameId c
    -- ^ Map from constructor (or projection) names to their arity
    --   and the case subtree.  (Projections have arity 0.)
  , fsucBranch      :: Maybe c
  , flitBranches    :: Map Literal c
    -- ^ Map from literal to case subtree.
  , fcatchAllBranch :: Maybe c
    -- ^ (Possibly additional) catch-all clause.
  , ffallThrough :: Maybe Bool
    -- ^ (if True) In case of non-canonical argument use catchAllBranch.
  }

-- | Case tree with bodies.

data FastCompiledClauses
  = FCase Int (FastCase FastCompiledClauses)
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
    -- If the @n@-th argument is a projection, we have only 'conBranches'
    -- with arity 0.
  | FDone [Arg ArgName] Term
    -- ^ @Done xs b@ stands for the body @b@ where the @xs@ contains hiding
    --   and name suggestions for the free variables. This is needed to build
    --   lambdas on the right hand side for partial applications which can
    --   still reduce.
  | FFail
    -- ^ Absurd case.

type FastStack = [(FastCompiledClauses, MaybeReducedElims, Elims -> Elims)]

fastCompiledClauses :: Maybe ConHead -> Maybe ConHead -> CompiledClauses -> FastCompiledClauses
fastCompiledClauses z s cc =
  case cc of
    Fail              -> FFail
    Done xs b         -> FDone xs b
    Case (Arg _ n) bs -> FCase n (fastCase z s bs)

fastCase :: Maybe ConHead -> Maybe ConHead -> Case CompiledClauses -> FastCase FastCompiledClauses
fastCase z s (Branches proj con lit wild fT) =
  FBranches
    { fprojPatterns   = proj
    , fconBranches    = Map.mapKeysMonotonic (nameId . qnameName) $ fmap (fastCompiledClauses z s . content) con
    , fsucBranch      = fmap (fastCompiledClauses z s . content) $ flip Map.lookup con . conName =<< s
    , flitBranches    = fmap (fastCompiledClauses z s) lit
    , ffallThrough    = fT
    , fcatchAllBranch = fmap (fastCompiledClauses z s) wild }

{-# INLINE lookupCon #-}
lookupCon :: QName -> FastCase c -> Maybe c
lookupCon c (FBranches _ cons _ _ _ _) = Map.lookup (nameId $ qnameName c) cons

-- QName memo -------------------------------------------------------------

{-# NOINLINE memoQName #-}
memoQName :: (QName -> a) -> (QName -> a)
memoQName f = unsafePerformIO $ do
  tbl <- newIORef Map.empty
  return (unsafePerformIO . f' tbl)
  where
    f' tbl x = do
      let i = nameId (qnameName x)
      m <- readIORef tbl
      case Map.lookup i m of
        Just y  -> return y
        Nothing -> do
          let y = f x
          writeIORef tbl (Map.insert i y m)
          return y

-- Faster substitution ----------------------------------------------------

-- Precondition: All free variables of the term are assigned values in the
-- list.
-- Reverts to normal substitution if it hits a binder or other icky stuff (like
-- levels). It's strict in the shape of the result to avoid creating huge
-- thunks for accumulator arguments.
strictSubst :: Bool -> [Term] -> Term -> Term
strictSubst strict us
  | not strict = applySubst rho
  | otherwise  = go 0
  where
    rho = parallelS us
    go k v =
      case v of
        Var x es
          | x < k     -> Var x $! map' (goE k) es
          | otherwise -> applyE (raise k $ us !! (x - k)) $! map' (goE k) es
        Def f es -> defApp f [] $! map' (goE k) es
        Con c ci vs -> Con c ci $! map' (mapArg' $ go k) vs
        Lam i b  -> Lam i $! goAbs k b
        Lit{}    -> v
        _        -> applySubst (liftS k rho) v

    goE k (Apply v) = Apply $! mapArg' (go k) v
    goE k (IApply x y r) = IApply (go k x) (go k y) (go k r)
    goE _ p@Proj{}       = p

    goAbs k (Abs   x v) = Abs   x $! go (k + 1) v
    goAbs k (NoAbs x v) = NoAbs x $! go k v

map' :: (a -> b) -> [a] -> [b]
map' f []       = []
map' f (x : xs) = ((:) $! f x) $! map' f xs

mapArg' :: (a -> b) -> Arg a -> Arg b
mapArg' f (Arg i x) = Arg i $! f x


-- Fast reduction ---------------------------------------------------------

-- | First argument: allow non-terminating reductions.
fastReduce :: Bool -> Term -> ReduceM (Blocked Term)
fastReduce allowNonTerminating v = do
  let name (Con c _ _) = c
      name _         = __IMPOSSIBLE__
  z  <- fmap name <$> getBuiltin' builtinZero
  s  <- fmap name <$> getBuiltin' builtinSuc
  pf <- fmap primFunName <$> getPrimitive' "primForce"
  rwr <- optRewriting <$> pragmaOptions
  constInfo <- unKleisli $ \f -> do
    info <- getConstInfo f
    rewr <- getRewriteRulesFor f
    compactDef z s pf info rewr
  ReduceM $ \ env -> reduceTm env (memoQName constInfo) allowNonTerminating rwr z s v

unKleisli :: (a -> ReduceM b) -> ReduceM (a -> b)
unKleisli f = ReduceM $ \ env x -> unReduceM (f x) env

reduceTm :: ReduceEnv -> (QName -> CompactDef) -> Bool -> Bool -> Maybe ConHead -> Maybe ConHead -> Term -> Blocked Term
reduceTm env !constInfo allowNonTerminating hasRewriting zero suc = reduceB' 0
  where
    -- Force substitutions every nth step to avoid memory leaks. Doing it in
    -- every is too expensive (issue 2215).
    strictEveryNth = 1000

    runReduce m = unReduceM m env
    conNameId = nameId . qnameName . conName
    isZero =
      case zero of
        Nothing -> const False
        Just z  -> (conNameId z ==) . conNameId

    isSuc  =
      case suc of
        Nothing -> const False
        Just s  -> (conNameId s ==) . conNameId

    reduceB' steps v =
      case v of
        Def f es -> runReduce $ reduceIApp es $ return $ unfoldDefinitionE steps False reduceB' (Def f []) f es
        Con c ci vs ->
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          case unfoldDefinition steps False reduceB' (Con c ci []) (conName c) vs of
            NotBlocked r v -> NotBlocked r $ reduceNat v
            b              -> b
        Lit{} -> done
        Var i es -> runReduce $ reduceIApp es (return done)
        _     -> runReduce (slowReduceTerm v)
      where
        reduceIApp es d = reduceIApply' (return . reduceB' steps) d es
        done = notBlocked v

        reduceNat v@(Con c ci [])
          | isZero c = Lit $ LitNat (getRange c) 0
        reduceNat v@(Con c ci [a])
          | isSuc c  = inc . ignoreBlocking $ reduceB' 0 (unArg a)
          where
            inc (Lit (LitNat r n)) = Lit (LitNat noRange $ n + 1)
            inc w                  = Con c ci [defaultArg w]
        reduceNat v = v

    originalProjection :: QName -> QName
    originalProjection q =
      case cdefDef $ constInfo q of
        CFun{ cfunProjection = Just p } -> p
        _                               -> __IMPOSSIBLE__

    -- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
    -- need also to instantiate metas, see Issue 826.
    unfoldCorecursionE :: Elim -> Blocked Elim
    unfoldCorecursionE (Proj o p)           = notBlocked $ Proj o $ originalProjection p
    unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) $
      unfoldCorecursion 0 v
    unfoldCorecursionE (IApply x y r) =
      IApply <$> unfoldCorecursion 0 x <*> unfoldCorecursion 0 y <*> unfoldCorecursion 0 r

    unfoldCorecursion :: Int -> Term -> Blocked Term
    unfoldCorecursion steps (Def f es) = unfoldDefinitionE steps True unfoldCorecursion (Def f []) f es
    unfoldCorecursion steps v          = reduceB' steps v

    -- | If the first argument is 'True', then a single delayed clause may
    -- be unfolded.
    unfoldDefinition ::
      Int -> Bool -> (Int -> Term -> Blocked Term) ->
      Term -> QName -> Args -> Blocked Term
    unfoldDefinition steps unfoldDelayed keepGoing v f args =
      unfoldDefinitionE steps unfoldDelayed keepGoing v f (map Apply args)

    unfoldDefinitionE ::
      Int -> Bool -> (Int -> Term -> Blocked Term) ->
      Term -> QName -> Elims -> Blocked Term
    unfoldDefinitionE steps unfoldDelayed keepGoing v f es =
      case unfoldDefinitionStep steps unfoldDelayed (constInfo f) v f es of
        NoReduction v    -> v
        YesReduction _ v -> (keepGoing $! steps + 1) v

    unfoldDefinitionStep :: Int -> Bool -> CompactDef -> Term -> QName -> Elims -> Reduced (Blocked Term) Term
    unfoldDefinitionStep steps unfoldDelayed CompactDef{cdefDelayed = delayed, cdefNonterminating = nonterm, cdefDef = def, cdefRewriteRules = rewr} v0 f es =
      let v = v0 `applyE` es
          -- Non-terminating functions
          -- (i.e., those that failed the termination check)
          -- and delayed definitions
          -- are not unfolded unless explicitely permitted.
          dontUnfold =
               (not allowNonTerminating && nonterm)
            || (not unfoldDelayed       && delayed)
      in case def of
        CCon{cconSrcCon = c} ->
          if hasRewriting then
            runReduce $ rewrite (notBlocked ()) (Con c ConOSystem []) rewr es
          else
            NoReduction $ notBlocked $ Con c ConOSystem [] `applyE` es
        CFun{cfunCompiled = cc} ->
          reduceNormalE steps v0 f (map notReduced es) dontUnfold cc
        CForce -> reduceForce unfoldDelayed v0 f es
        CTyCon -> if hasRewriting then
                    runReduce $ rewrite (notBlocked ()) v0 rewr es
                  else
                    NoReduction $ notBlocked v
        COther -> runReduce $ R.unfoldDefinitionStep unfoldDelayed v0 f es
      where
        yesReduction = YesReduction NoSimplification

        reduceForce :: Bool -> Term -> QName -> Elims -> Reduced (Blocked Term) Term
        reduceForce unfoldDelayed v0 pf (Apply a : Apply b : Apply s : Apply t : Apply u : Apply f : es) =
          case reduceB' 0 (unArg u) of
            ub@Blocked{}        -> noGo ub
            ub@(NotBlocked _ u)
              | isWHNF u  -> yesReduction $ unArg f `applyE` (Apply (defaultArg u) : es)
              | otherwise -> noGo ub
          where
            noGo ub = NoReduction $ ub <&> \ u -> Def pf (Apply a : Apply b : Apply s : Apply t : Apply (defaultArg u) : Apply f : es)

            isWHNF u = case u of
              Lit{}      -> True
              Con{}      -> True
              Lam{}      -> True
              Pi{}       -> True
              Sort{}     -> True
              Level{}    -> True
              DontCare{} -> True
              MetaV{}    -> False
              Var{}      -> False
              Def q _    -> isTyCon q
              Shared{}   -> __IMPOSSIBLE__

            isTyCon q =
              case cdefDef $ constInfo q of
                CTyCon -> True
                _      -> False

        -- TODO: partially applied to u
        reduceForce unfoldDelayed v0 pf es = runReduce $ R.unfoldDefinitionStep unfoldDelayed v0 f es

        reduceNormalE :: Int -> Term -> QName -> [MaybeReduced Elim] -> Bool -> FastCompiledClauses -> Reduced (Blocked Term) Term
        reduceNormalE steps v0 f es dontUnfold cc
          | dontUnfold = defaultResult  -- non-terminating or delayed
          | otherwise  =
            case match' steps f [(cc, es, id)] of
              YesReduction s u -> YesReduction s u
              NoReduction es'  -> if hasRewriting then
                                    runReduce $ rewrite (void es') v0 rewr (ignoreBlocking es')
                                  else
                                    NoReduction $ applyE v0 <$> es'
          where defaultResult = if hasRewriting then
                                  runReduce $ rewrite (NotBlocked AbsurdMatch ()) v0 rewr (map ignoreReduced es)
                                else
                                  NoReduction $ NotBlocked AbsurdMatch vfull
                vfull         = v0 `applyE` map ignoreReduced es

        match' :: Int -> QName -> FastStack -> Reduced (Blocked Elims) Term
        match' steps f ((c, es, patch) : stack) =
          let no blocking es = NoReduction $ blocking $ patch $ map ignoreReduced es
              yes t          = yesReduction t

          in case c of

            -- impossible case
            FFail -> no (NotBlocked AbsurdMatch) es

            -- done matching
            FDone xs t
              -- common case: exact number of arguments
              | m == n    -> {-# SCC match'Done #-} yes $ doSubst es t
              -- if the function was partially applied, return a lambda
              | m < n     -> yes $ doSubst es $ foldr lam t (drop m xs)
              -- otherwise, just apply instantiation to body
              -- apply the result to any extra arguments
              | otherwise -> yes $ doSubst es0 t `applyE` map ignoreReduced es1
              where
                n = length xs
                m = length es
                useStrictSubst = rem steps strictEveryNth == 0
                doSubst es t = strictSubst useStrictSubst (reverse $ map (unArg . argFromElim . ignoreReduced) es) t
                (es0, es1) = splitAt n es
                lam x t    = Lam (argInfo x) (Abs (unArg x) t)

            -- splitting on the @n@th elimination
            FCase n bs -> {-# SCC "match'Case" #-}
              case splitAt n es of
                -- if the @n@th elimination is not supplied, no match
                (_, []) -> no (NotBlocked Underapplied) es
                -- if the @n@th elimination is @e0@
                (es0, MaybeRed red e0 : es1) ->
                  -- get the reduced form of @e0@
                  let eb = case red of
                             Reduced b  -> e0 <$ b
                             NotReduced -> unfoldCorecursionE e0
                      e = ignoreBlocking eb
                      -- replace the @n@th argument by its reduced form
                      es' = es0 ++ [MaybeRed (Reduced $ () <$ eb) e] ++ es1
                      -- if a catch-all clause exists, put it on the stack
                      catchAllFrame stack = maybe stack (\c -> (c, es', patch) : stack) (fcatchAllBranch bs)
                      -- If our argument is @Lit l@, we push @litFrame l@ onto the stack.
                      litFrame l stack =
                        case Map.lookup l (flitBranches bs) of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ es1, patchLit) : stack
                      -- If our argument (or its constructor form) is @Con c ci vs@
                      -- we push @conFrame c ci vs@ onto the stack.
                      conFrame c ci vs stack =
                        case lookupCon (conName c) bs of
                          Nothing -> stack
                          Just cc -> ( cc
                                     , es0 ++ map (MaybeRed NotReduced . Apply) vs ++ es1
                                     , patchCon c ci (length vs)
                                     ) : stack

                      sucFrame n stack =
                        case fsucBranch bs of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ [v] ++ es1, patchCon (fromJust suc) ConOSystem 1)
                                     : stack
                        where v = MaybeRed (Reduced $ notBlocked ()) $ Apply $ defaultArg $ Lit $ LitNat noRange n

                      -- If our argument is @Proj p@, we push @projFrame p@ onto the stack.
                      projFrame p stack =
                        case lookupCon p bs of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ es1, patchLit) : stack
                      -- The new patch function restores the @n@th argument to @v@:
                      -- In case we matched a literal, just put @v@ back.
                      patchLit es = patch (es0 ++ [e] ++ es1)
                        where (es0, es1) = splitAt n es
                      -- In case we matched constructor @c@ with @m@ arguments,
                      -- contract these @m@ arguments @vs@ to @Con c ci vs@.
                      patchCon c ci m es = patch (es0 ++ [Con c ci vs <$ e] ++ es2)
                        where (es0, rest) = splitAt n es
                              (es1, es2)  = splitAt m rest
                              vs          = map argFromElim es1
                      fallThrough = fromMaybe False (ffallThrough bs) && isJust (fcatchAllBranch bs)
                  -- Now do the matching on the @n@ths argument:
                  in case eb of
                    Blocked x _ | fallThrough -> match' steps f $ catchAllFrame $ stack
                    Blocked x _       -> no (Blocked x) es'
                    NotBlocked blk elim ->
                      case elim of
                        IApply{} -> __IMPOSSIBLE__ -- Cannot define a path by cases
                        Apply (Arg info v) ->
                          case v of

                            -- In case of a natural number literal, try also its constructor form
                            Lit l@(LitNat r n) ->
                              let cFrame stack
                                    | n > 0                  = sucFrame (n - 1) stack
                                    | n == 0, Just z <- zero = conFrame z ConOSystem [] stack
                                    | otherwise              = stack
                              in match' steps f $ litFrame l $ cFrame $ catchAllFrame stack

                            Lit l    -> match' steps f $ litFrame l    $ catchAllFrame stack
                            Con c ci vs -> match' steps f $ conFrame c ci vs $ catchAllFrame $ stack

                            _ | fallThrough -> match' steps f $ catchAllFrame $ stack

                            MetaV x _ -> no (Blocked x) es'

                            -- Otherwise, we are stuck.  If we were stuck before,
                            -- we keep the old reason, otherwise we give reason StuckOn here.
                            _ -> no (NotBlocked $ stuckOn elim blk) es'

                        -- In case of a projection, push the projFrame
                        Proj _ p -> match' steps f $ projFrame p stack


        -- If we reach the empty stack, then pattern matching was incomplete
        match' _ f [] = runReduce $ do
          pds <- getPartialDefs
          if f `elem` pds
          then return (NoReduction $ NotBlocked MissingClauses es)
          else do
            reportSLn "impossible" 10
              ("Incomplete pattern matching when applying " ++ show f)
            __IMPOSSIBLE__
