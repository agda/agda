{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE BangPatterns        #-}

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
import Agda.TypeChecking.Reduce.Monad as RedM
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Builtin hiding (constructorForm)
import Agda.TypeChecking.CompiledClause.Match

import Agda.Utils.Maybe
import Agda.Utils.Memo

#include "undefined.h"
import Agda.Utils.Impossible

-- Compact definitions ----------------------------------------------------

data CompactDef =
  CompactDef { cdefDelayed        :: Bool
             , cdefNonterminating :: Bool
             , cdefDef            :: CompactDefn }

data CompactDefn
  = CFun  { cfunCompiled  :: FastCompiledClauses }
  | CCon  { cconSrcCon    :: ConHead }
  | COther

compactDef :: Maybe ConHead -> Maybe ConHead -> Definition -> ReduceM CompactDef
compactDef z s def = do
  cdefn <-
    case theDef def of
      Constructor{conSrcCon = c} -> pure CCon{cconSrcCon = c}
      Function{funCompiled = Just cc, funClauses = _:_} ->
        pure CFun{ cfunCompiled = fastCompiledClauses z s cc }
      _ -> pure COther
  return $
    CompactDef { cdefDelayed        = defDelayed def == Delayed
               , cdefNonterminating = defNonterminating def
               , cdefDef            = cdefn
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
fastCase z s (Branches proj con lit wild) =
  FBranches
    { fprojPatterns   = proj
    , fconBranches    = Map.mapKeysMonotonic (nameId . qnameName) $ fmap (fastCompiledClauses z s . content) con
    , fsucBranch      = fmap (fastCompiledClauses z s . content) $ flip Map.lookup con . conName =<< s
    , flitBranches    = fmap (fastCompiledClauses z s) lit
    , fcatchAllBranch = fmap (fastCompiledClauses z s) wild }

{-# INLINE lookupCon #-}
lookupCon :: QName -> FastCase c -> Maybe c
lookupCon c (FBranches _ cons _ _ _) = Map.lookup (nameId $ qnameName c) cons

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
-- levels).
fastSubst :: [Term] -> Term -> Term
fastSubst us = go
  where
    rho = parallelS us
    go v =
      case v of
        Var x es -> (us !! x) `applyE` map goE es
        Def f es -> defApp f [] $ map goE es
        Con c vs -> Con c $ map (fmap go) vs
        Lit{}    -> v
        _        -> applySubst rho v
    goE (Apply v) = Apply (fmap go v)
    goE p         = p

-- Fast reduction ---------------------------------------------------------

-- | First argument: allow non-terminating reductions.
fastReduce :: Bool -> Term -> ReduceM (Blocked Term)
fastReduce allowNonTerminating v = do
  let name (Con c _) = c
      name _         = __IMPOSSIBLE__
  z <- fmap name <$> getBuiltin' builtinZero
  s <- fmap name <$> getBuiltin' builtinSuc
  constInfo <- unKleisli (compactDef z s <=< getConstInfo)
  ReduceM $ \ env -> reduceTm env (memoQName constInfo) allowNonTerminating z s v

unKleisli :: (a -> ReduceM b) -> ReduceM (a -> b)
unKleisli f = ReduceM $ \ env x -> unReduceM (f x) env

reduceTm :: ReduceEnv -> (QName -> CompactDef) -> Bool -> Maybe ConHead -> Maybe ConHead -> Term -> Blocked Term
reduceTm env !constInfo allowNonTerminating zero suc = reduceB'
  where
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

    reduceB' v =
      case v of
        Def f es -> unfoldDefinitionE False reduceB' (Def f []) f es
        Con c vs ->
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          case unfoldDefinition False reduceB' (Con c []) (conName c) vs of
            NotBlocked r v -> NotBlocked r $ reduceNat v
            b              -> b
        Lit{} -> done
        Var{} -> done
        _     -> runReduce (slowReduceTerm v)
      where
        done = notBlocked v

        reduceNat v@(Con c [])
          | isZero c = Lit $ LitNat (getRange c) 0
        reduceNat v@(Con c [a])
          | isSuc c  = inc . ignoreBlocking $ reduceB' (unArg a)
          where
            inc (Lit (LitNat r n)) = Lit (LitNat noRange $ n + 1)
            inc w                  = Con c [defaultArg w]
        reduceNat v = v

    -- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
    -- need also to instantiate metas, see Issue 826.
    unfoldCorecursionE :: Elim -> Blocked Elim
    unfoldCorecursionE e@Proj{}             = notBlocked e
    unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) $
      unfoldCorecursion v

    unfoldCorecursion :: Term -> Blocked Term
    unfoldCorecursion (Def f es) = unfoldDefinitionE True unfoldCorecursion (Def f []) f es
    unfoldCorecursion v          = reduceB' v

    -- | If the first argument is 'True', then a single delayed clause may
    -- be unfolded.
    unfoldDefinition ::
      Bool -> (Term -> Blocked Term) ->
      Term -> QName -> Args -> Blocked Term
    unfoldDefinition unfoldDelayed keepGoing v f args =
      unfoldDefinitionE unfoldDelayed keepGoing v f (map Apply args)

    unfoldDefinitionE ::
      Bool -> (Term -> Blocked Term) ->
      Term -> QName -> Elims -> Blocked Term
    unfoldDefinitionE unfoldDelayed keepGoing v f es =
      case unfoldDefinitionStep unfoldDelayed (constInfo f) v f es of
        NoReduction v    -> v
        YesReduction _ v -> keepGoing v

    unfoldDefinitionStep :: Bool -> CompactDef -> Term -> QName -> Elims -> Reduced (Blocked Term) Term
    unfoldDefinitionStep unfoldDelayed CompactDef{cdefDelayed = delayed, cdefNonterminating = nonterm, cdefDef = def} v0 f es =
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
          noReduction $ notBlocked $ Con c [] `applyE` es
        CFun{cfunCompiled = cc} ->
          reduceNormalE v0 f (map notReduced es) dontUnfold cc
        _ -> runReduce $ R.unfoldDefinitionStep unfoldDelayed v0 f es
      where
        noReduction    = NoReduction
        yesReduction s = YesReduction s

        reduceNormalE :: Term -> QName -> [MaybeReduced Elim] -> Bool -> FastCompiledClauses -> Reduced (Blocked Term) Term
        reduceNormalE v0 f es dontUnfold cc
          | dontUnfold = defaultResult  -- non-terminating or delayed
          | otherwise  = appDefE f v0 cc es
          where defaultResult = noReduction $ NotBlocked AbsurdMatch vfull
                vfull         = v0 `applyE` map ignoreReduced es

        appDefE :: QName -> Term -> FastCompiledClauses -> MaybeReducedElims -> Reduced (Blocked Term) Term
        appDefE f v cc es =
          case match' f [(cc, es, id)] of
            YesReduction s u -> YesReduction s u
            NoReduction es'  -> NoReduction $ applyE v <$> es'

        match' :: QName -> FastStack -> Reduced (Blocked Elims) Term
        match' f ((c, es, patch) : stack) =
          let no blocking es = NoReduction $ blocking $ patch $ map ignoreReduced es
              yes t          = YesReduction NoSimplification t

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
                doSubst es t = fastSubst (reverse $ map (unArg . argFromElim . ignoreReduced) es) t
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
                      -- If our argument (or its constructor form) is @Con c vs@
                      -- we push @conFrame c vs@ onto the stack.
                      conFrame c vs stack =
                        case lookupCon (conName c) bs of
                          Nothing -> stack
                          Just cc -> ( cc
                                     , es0 ++ map (MaybeRed NotReduced . Apply) vs ++ es1
                                     , patchCon c (length vs)
                                     ) : stack

                      sucFrame n stack =
                        case fsucBranch bs of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ [v] ++ es1, patchCon (fromJust suc) 1)
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
                      -- contract these @m@ arguments @vs@ to @Con c vs@.
                      patchCon c m es = patch (es0 ++ [Con c vs <$ e] ++ es2)
                        where (es0, rest) = splitAt n es
                              (es1, es2)  = splitAt m rest
                              vs          = map argFromElim es1
                  -- Now do the matching on the @n@ths argument:
                  in case eb of
                    Blocked x _       -> no (Blocked x) es'
                    NotBlocked blk elim ->
                      case elim of
                        Apply (Arg info v) ->
                          case v of
                            MetaV x _ -> no (Blocked x) es'

                            -- In case of a natural number literal, try also its constructor form
                            Lit l@(LitNat r n) ->
                              let cFrame stack
                                    | n > 0                  = sucFrame (n - 1) stack
                                    | n == 0, Just z <- zero = conFrame z [] stack
                                    | otherwise              = stack
                              in match' f $ litFrame l $ cFrame $ catchAllFrame stack

                            Lit l    -> match' f $ litFrame l    $ catchAllFrame stack
                            Con c vs -> match' f $ conFrame c vs $ catchAllFrame $ stack

                            -- Otherwise, we are stuck.  If we were stuck before,
                            -- we keep the old reason, otherwise we give reason StuckOn here.
                            _ -> no (NotBlocked $ stuckOn elim blk) es'

                        -- In case of a projection, push the projFrame
                        Proj _ p -> match' f $ projFrame p stack


        -- If we reach the empty stack, then pattern matching was incomplete
        match' f [] = {- new line here since __IMPOSSIBLE__ does not like the ' in match' -}
          runReduce $
            traceSLn "impossible" 10
              ("Incomplete pattern matching when applying " ++ show f)
              __IMPOSSIBLE__
