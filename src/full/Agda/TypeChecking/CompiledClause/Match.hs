{-# LANGUAGE CPP, PatternGuards, ScopedTypeVariables #-}
module Agda.TypeChecking.CompiledClause.Match where

import Control.Applicative
import Control.Monad.Reader (asks)
import qualified Data.Map as Map
import Data.List

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive

import Agda.Utils.Maybe

#include "../../undefined.h"
import Agda.Utils.Impossible

matchCompiled :: CompiledClauses -> MaybeReducedArgs -> TCM (Reduced (Blocked Args) Term)
matchCompiled c args = do
  r <- matchCompiledE c $ map (fmap Apply) args
  case r of
    YesReduction simpl v -> return $ YesReduction simpl v
    NoReduction bes      -> return $ NoReduction $ fmap (map fromElim) bes
  where fromElim (Apply v) = v
        fromElim (Proj f ) = __IMPOSSIBLE__

-- | @matchCompiledE c es@ takes a function given by case tree @c@ and
--   and a spine @es@ and tries to apply the function to @es@.
matchCompiledE :: CompiledClauses -> MaybeReducedElims -> TCM (Reduced (Blocked Elims) Term)
matchCompiledE c args = match' [(c, args, id)]

-- | A stack entry is a triple consisting of
--   1. the part of the case tree to continue matching,
--   2. the current argument vector, and
--   3. a patch function taking the current argument vector back
--      to the original argument vector.
type Frame = (CompiledClauses, MaybeReducedElims, Elims -> Elims)
type Stack = [Frame]


-- | @match'@ tries to solve the matching problems on the @Stack@.
--   In each iteration, the top problem is removed and handled.
--
--   If the top problem was a @Done@, we succeed.
--
--   If the top problem was a @Case n@ and the @n@th argument of the problem
--   is not a constructor or literal, we are stuck, thus, fail.
--
--   If we have a branch for the constructor/literal, we put it on the stack
--   to continue.
--   If we do not have a branch, we fall through to the next problem, which
--   should be the corresponding catch-all branch.
--
--   An empty stack is an exception that can come only from an incomplete
--   function definition.

-- TODO: literal/constructor pattern conflict (for Nat)

match' :: Stack -> TCM (Reduced (Blocked Elims) Term)
match' ((c, es, patch) : stack) = do
  let no          es = return $ NoReduction $ NotBlocked $ patch $ map ignoreReduced es
      noBlocked x es = return $ NoReduction $ Blocked x  $ patch $ map ignoreReduced es
      yes t            = flip YesReduction t <$> asks envSimplification
  case c of

    -- impossible case
    Fail -> no es

    -- done matching
    Done xs t
      -- if the function was partially applied, return a lambda
      | m < n     -> yes $ applySubst (toSubst es) $ foldr lam t (drop m xs)
      -- otherwise, just apply instantiation to body
      -- apply the result to any extra arguments
      | otherwise -> yes $ applySubst (toSubst es0) t `applyE` map ignoreReduced es1
--      | otherwise -> yes $ applySubst (toSubst args0) t `apply` map ignoreReduced args1
      where
        n              = length xs
        m              = length es
        -- at least the first @n@ elims must be @Apply@s, so we can
        -- turn them into a subsitution
        toSubst        = parallelS . reverse . map (unArg . argFromElim . ignoreReduced)
--        (args0, args1) = splitAt n $ map (fmap $ fmap shared) args
--        (args0, es1)   = takeArgsFromElims n $ map (fmap $ fmap shared) args
        -- Andreas, 2013-05-21 why introduce sharing only here,
        -- and not in underapplied case also?
        (es0, es1)     = splitAt n $ map (fmap $ fmap shared) es
        lam x t        = Lam (argInfo x) (Abs (unArg x) t)

    -- splitting on the @n@th elimination
    Case n bs -> do
      case genericSplitAt n es of
        -- if the @n@th elimination is not supplied, no match
        (_, []) -> no es
        -- if the @n@th elimination is @e0@
--        (args0, MaybeRed red (Arg info v0) : args1) -> do
        (es0, MaybeRed red e0 : es1) -> do
          -- get the reduced form of @e0@
{-
          w  <- case red of
                  Reduced b  -> return $ v0 <$ b
                  NotReduced -> unfoldCorecursion v0
          let v = ignoreBlocking w
              args'  = args0 ++ [MaybeRed red $ Arg info v] ++ args1
-}
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
          case fmap ignoreSharing <$> eb of
            Blocked x _            -> noBlocked x es'
            NotBlocked (Apply (Arg info (MetaV x _))) -> noBlocked x es'

            -- In case of a literal, try also its constructor form
            NotBlocked (Apply (Arg info v@(Lit l))) -> performedSimplification $ do
              cv <- constructorForm v
              let cFrame stack = case ignoreSharing cv of
                    Con c vs -> conFrame c vs stack
                    _        -> stack
              match' $ litFrame l $ cFrame $ catchAllFrame stack

            -- In case of a constructor, push the conFrame
            NotBlocked (Apply (Arg info (Con c vs))) -> performedSimplification $
              match' $ conFrame c vs $ catchAllFrame $ stack

            -- In case of a projection, push the litFrame
            NotBlocked (Proj p) -> performedSimplification $
              match' $ projFrame p $ stack

            NotBlocked _ -> no es'

-- If we reach the empty stack, then pattern matching was incomplete
match' [] = do  {- new line here since __IMPOSSIBLE__ does not like the ' in match' -}
  caseMaybeM (asks envAppDef) __IMPOSSIBLE__ $ \ f -> do
    typeError $ GenericError $ "Incomplete pattern matching when applying " ++ show f


-- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
-- need also to instantiate metas, see Issue 826.
unfoldCorecursionE :: Elim -> TCM (Blocked Elim)
unfoldCorecursionE e@(Proj f)           = return $ NotBlocked e
unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) <$>
  unfoldCorecursion v

unfoldCorecursion :: Term -> TCM (Blocked Term)
unfoldCorecursion v = do
  v <- instantiate v
  case v of
    Def f es -> unfoldDefinitionE True unfoldCorecursion (Def f []) f es
    Shared{} -> fmap shared <$> unfoldCorecursion (ignoreSharing v) -- don't update when unfolding corecursion!
    _          -> reduceB v
