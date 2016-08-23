{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards       #-}

module Agda.TypeChecking.Reduce.Fast
  ( fastReduce ) where

import Control.Applicative
import Control.Monad.Reader

import Data.List
import qualified Data.Map as Map
import Data.Traversable (traverse)

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad as RedM
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Monad.Builtin hiding (constructorForm)
import Agda.TypeChecking.CompiledClause.Match

import Agda.Utils.Maybe

#include "undefined.h"
import Agda.Utils.Impossible

-- | First argument: allow non-terminating reductions.
fastReduce :: Bool -> Term -> ReduceM (Blocked Term)
fastReduce allowNonTerminating v = do
  let name (Con c _) = c
      name _         = __IMPOSSIBLE__
  z <- fmap name <$> getBuiltin' builtinZero
  s <- fmap name <$> getBuiltin' builtinSuc
  reduceTm allowNonTerminating z s v

reduceTm :: Bool -> Maybe ConHead -> Maybe ConHead -> Term -> ReduceM (Blocked Term)
reduceTm allowNonTerminating zero suc = reduceB'
  where
    reduceB' v =
      case v of
        Def f es -> unfoldDefinitionE False reduceB' (Def f []) f es
        Con c vs -> do
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          v <- unfoldDefinition False reduceB' (Con c []) (conName c) vs
          traverse reduceNat v
        _ -> slowReduceTerm v

    reduceNat v@(Con c [])
      | Just c == zero = return $ Lit $ LitNat (getRange c) 0
    reduceNat v@(Con c [a])
      | Just c == suc  = inc . ignoreBlocking <$> reduceB' (unArg a)
      where
        inc (Lit (LitNat r n)) = Lit (LitNat noRange $ n + 1)
        inc w                  = Con c [defaultArg w]
    reduceNat v = return v

    -- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
    -- need also to instantiate metas, see Issue 826.
    unfoldCorecursionE :: Elim -> ReduceM (Blocked Elim)
    unfoldCorecursionE e@Proj{}             = return $ notBlocked e
    unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) <$>
      unfoldCorecursion v

    unfoldCorecursion :: Term -> ReduceM (Blocked Term)
    unfoldCorecursion (Def f es) = unfoldDefinitionE True unfoldCorecursion (Def f []) f es
    unfoldCorecursion v          = reduceB' v

    -- | If the first argument is 'True', then a single delayed clause may
    -- be unfolded.
    unfoldDefinition ::
      Bool -> (Term -> ReduceM (Blocked Term)) ->
      Term -> QName -> Args -> ReduceM (Blocked Term)
    unfoldDefinition unfoldDelayed keepGoing v f args =
      unfoldDefinitionE unfoldDelayed keepGoing v f (map Apply args)

    unfoldDefinitionE ::
      Bool -> (Term -> ReduceM (Blocked Term)) ->
      Term -> QName -> Elims -> ReduceM (Blocked Term)
    unfoldDefinitionE unfoldDelayed keepGoing v f es = do
      r <- unfoldDefinitionStep unfoldDelayed v f es
      case r of
        NoReduction v    -> return v
        YesReduction _ v -> keepGoing v

    unfoldDefinitionStep :: Bool -> Term -> QName -> Elims -> ReduceM (Reduced (Blocked Term) Term)
    unfoldDefinitionStep unfoldDelayed v0 f es =
      {-# SCC "reduceDef" #-} do
      info <- getConstInfo f
      let def = theDef info
          v   = v0 `applyE` es
          -- Non-terminating functions
          -- (i.e., those that failed the termination check)
          -- and delayed definitions
          -- are not unfolded unless explicitely permitted.
          dontUnfold =
               (not allowNonTerminating && defNonterminating info)
            || (not unfoldDelayed       && defDelayed info == Delayed)
      case def of
        Constructor{conSrcCon = c} ->
          noReduction $ notBlocked $ Con c [] `applyE` es
        Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
          pf <- fromMaybe __IMPOSSIBLE__ <$> getPrimitive' x
          reducePrimitive x v0 f es pf dontUnfold
                          cls (defCompiled info)
        _  -> reduceNormalE v0 f (map notReduced es) dontUnfold
                            (defClauses info) (defCompiled info)
      where
        noReduction    = return . NoReduction
        yesReduction s = return . YesReduction s
        reducePrimitive x v0 f es pf dontUnfold cls mcc
          | genericLength es < ar
                      = noReduction $ NotBlocked Underapplied $ v0 `applyE` es -- not fully applied
          | otherwise = {-# SCC "reducePrimitive" #-} do
              let (es1,es2) = genericSplitAt ar es
                  args1     = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es1
              r <- primFunImplementation pf args1
              case r of
                NoReduction args1' -> do
                  let es1' = map (fmap Apply) args1'
                  if null cls then do
                    noReduction $ applyE (Def f []) <$> do
                      traverse id $
                        map mredToBlocked es1' ++ map notBlocked es2
                   else
                    reduceNormalE v0 f (es1' ++ map notReduced es2) dontUnfold cls mcc
                YesReduction simpl v -> yesReduction simpl $ v `applyE` es2
          where
              ar  = primFunArity pf
              mredToBlocked :: MaybeReduced a -> Blocked a
              mredToBlocked (MaybeRed NotReduced  x) = notBlocked x
              mredToBlocked (MaybeRed (Reduced b) x) = x <$ b

        reduceNormalE :: Term -> QName -> [MaybeReduced Elim] -> Bool -> [Clause] -> Maybe CompiledClauses -> ReduceM (Reduced (Blocked Term) Term)
        reduceNormalE v0 f es dontUnfold def mcc = {-# SCC "reduceNormal" #-} do
          case def of
            _ | dontUnfold -> defaultResult -- non-terminating or delayed
            []             -> defaultResult -- no definition for head
            cls            -> appDefE_ f v0 cls mcc es
          where defaultResult = noReduction $ NotBlocked AbsurdMatch vfull
                vfull         = v0 `applyE` map ignoreReduced es

        appDefE_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
        appDefE_ f v0 cls mcc args =
          local (\ e -> e { envAppDef = Just f }) $
          maybe (appDefE' v0 cls args)
                (\cc -> appDefE v0 cc args) mcc

        appDefE :: Term -> CompiledClauses -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
        appDefE v cc es = do
          r <- matchCompiledE cc es
          case r of
            YesReduction s u -> return $ YesReduction s u
            NoReduction es'  -> return $ NoReduction $ applyE v <$> es'

        matchCompiledE :: CompiledClauses -> MaybeReducedElims -> ReduceM (Reduced (Blocked Elims) Term)
        matchCompiledE c args = match' [(c, args, id)]

        match' :: Stack -> ReduceM (Reduced (Blocked Elims) Term)
        match' ((c, es, patch) : stack) = do
          let no blocking es = return $ NoReduction $ blocking $ patch $ map ignoreReduced es
              yes t          = return $ YesReduction NoSimplification t

          case c of

            -- impossible case
            Fail -> no (NotBlocked AbsurdMatch) es

            -- done matching
            Done xs t
              -- if the function was partially applied, return a lambda
              | m < n     -> yes $ applySubst (toSubst es) $ foldr lam t (drop m xs)
              -- otherwise, just apply instantiation to body
              -- apply the result to any extra arguments
              | otherwise -> yes $ applySubst (toSubst es0) t `applyE` map ignoreReduced es1
              where
                n          = length xs
                m          = length es
                -- at least the first @n@ elims must be @Apply@s, so we can
                -- turn them into a subsitution
                toSubst    = parallelS . reverse . map (unArg . argFromElim . ignoreReduced)
                (es0, es1) = splitAt n es
                lam x t    = Lam (argInfo x) (Abs (unArg x) t)

            -- splitting on the @n@th elimination
            Case (Arg _ n) bs -> do
              case genericSplitAt n es of
                -- if the @n@th elimination is not supplied, no match
                (_, []) -> no (NotBlocked Underapplied) es
                -- if the @n@th elimination is @e0@
                (es0, MaybeRed red e0 : es1) -> do
                  -- get the reduced form of @e0@
                  eb :: Blocked Elim <- do
                        case red of
                          Reduced b  -> return $ e0 <$ b
                          NotReduced -> unfoldCorecursionE e0
                  let e = ignoreBlocking eb
                      -- replace the @n@th argument by its reduced form
                      es' = es0 ++ [MaybeRed red e] ++ es1
                      -- if a catch-all clause exists, put it on the stack
                      catchAllFrame stack = maybe stack (\c -> (c, es', patch) : stack) (catchAllBranch bs)
                      -- If our argument is @Lit l@, we push @litFrame l@ onto the stack.
                      litFrame l stack =
                        case Map.lookup l (litBranches bs) of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ es1, patchLit) : stack
                      -- If our argument (or its constructor form) is @Con c vs@
                      -- we push @conFrame c vs@ onto the stack.
                      conFrame c vs stack =
                        case Map.lookup (conName c) (conBranches bs) of
                          Nothing -> stack
                          Just cc -> ( content cc
                                     , es0 ++ map (MaybeRed red . Apply) vs ++ es1
                                     , patchCon c (length vs)
                                     ) : stack
                      -- If our argument is @Proj p@, we push @projFrame p@ onto the stack.
                      projFrame p stack =
                        case Map.lookup p (conBranches bs) of
                          Nothing -> stack
                          Just cc -> (content cc, es0 ++ es1, patchLit) : stack
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
                  id $
                   case fmap ignoreSharing <$> eb of
                    Blocked x _            -> no (Blocked x) es'
                    NotBlocked _ (Apply (Arg info (MetaV x _))) -> no (Blocked x) es'

                    -- In case of a natural number literal, try also its constructor form
                    NotBlocked _ (Apply (Arg info v@(Lit l@(LitNat r n)))) -> do
                      let cFrame stack
                            | n == 0, Just z <- zero = conFrame z [] stack
                            | n > 0,  Just s <- suc  = conFrame s [Arg info (Lit (LitNat r (n - 1)))] stack
                            | otherwise              = stack
                      match' $ litFrame l $ cFrame $ catchAllFrame stack

                    NotBlocked _ (Apply (Arg info v@(Lit l))) -> do
                      match' $ litFrame l $ catchAllFrame stack

                    -- In case of a constructor, push the conFrame
                    NotBlocked _ (Apply (Arg info (Con c vs))) ->
                      match' $ conFrame c vs $ catchAllFrame $ stack

                    -- In case of a projection, push the projFrame
                    NotBlocked _ (Proj _ p) ->
                      match' $ projFrame p $ stack -- catchAllFrame $ stack
                      -- Issue #1986: no catch-all for copattern matching!

                    -- Otherwise, we are stuck.  If we were stuck before,
                    -- we keep the old reason, otherwise we give reason StuckOn here.
                    NotBlocked blocked e -> no (NotBlocked $ stuckOn e blocked) es'

        -- If we reach the empty stack, then pattern matching was incomplete
        match' [] = {- new line here since __IMPOSSIBLE__ does not like the ' in match' -}
          caseMaybeM (asks envAppDef) __IMPOSSIBLE__ $ \ f -> do
            traceSLn "impossible" 10
              ("Incomplete pattern matching when applying " ++ show f)
              __IMPOSSIBLE__
