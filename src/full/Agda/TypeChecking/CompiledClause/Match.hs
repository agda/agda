{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

module Agda.TypeChecking.CompiledClause.Match where

import Control.Applicative
import Control.Monad.Reader (asks)

import Data.List
import qualified Data.Map as Map

import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad hiding (reportSDoc, reportSLn)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad as RedM
import Agda.TypeChecking.Substitute

import Agda.Utils.Maybe

#include "undefined.h"
import Agda.Utils.Impossible

matchCompiled :: CompiledClauses -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Args) Term)
matchCompiled c args = do
  r <- matchCompiledE c $ map (fmap Apply) args
  case r of
    YesReduction simpl v -> return $ YesReduction simpl v
    NoReduction bes      -> return $ NoReduction $ fmap (map fromElim) bes
  where fromElim (Apply v) = v
        fromElim (Proj f ) = __IMPOSSIBLE__

-- | @matchCompiledE c es@ takes a function given by case tree @c@ and
--   and a spine @es@ and tries to apply the function to @es@.
matchCompiledE :: CompiledClauses -> MaybeReducedElims -> ReduceM (Reduced (Blocked Elims) Term)
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

match' :: Stack -> ReduceM (Reduced (Blocked Elims) Term)
match' ((c, es, patch) : stack) = do
  let debug = do
       traceSDoc "reduce.compiled" 95 $ vcat $
         [ text "reducing case" <+> do
             caseMaybeM (asks envAppDef) __IMPOSSIBLE__ $ \ f -> do
               sep $ prettyTCM f : map prettyTCM es
         , text $ "trying clause " ++ show c
         ]
  let no blocking es = return $ NoReduction $ blocking $ patch $ map ignoreReduced es
      yes t          = flip YesReduction t <$> asks envSimplification

  -- traceSLn "reduce.compiled" 95 "CompiledClause.Match.match'" $ do
  debug $ do

    shared <- sharedFun

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
          n              = length xs
          m              = length es
          -- at least the first @n@ elims must be @Apply@s, so we can
          -- turn them into a subsitution
          toSubst        = parallelS . reverse . map (unArg . argFromElim . ignoreReduced)
          -- Andreas, 2013-05-21 why introduce sharing only here,
          -- and not in underapplied case also?
          (es0, es1)     = splitAt n $ map (fmap $ fmap shared) es
          lam x t        = Lam (argInfo x) (Abs (unArg x) t)

      -- splitting on the @n@th elimination
      Case n bs -> do
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
            traceSLn "reduce.compiled" 100 ("caseing on raw " ++ show eb) $
             case fmap ignoreSharing <$> eb of
              Blocked x _            -> no (Blocked x) es'
              NotBlocked _ (Apply (Arg info (MetaV x _))) -> no (Blocked x) es'

              -- In case of a literal, try also its constructor form
              NotBlocked _ (Apply (Arg info v@(Lit l))) -> performedSimplification $ do
                cv <- constructorForm v
                let cFrame stack = case ignoreSharing cv of
                      Con c vs -> conFrame c vs stack
                      _        -> stack
                traceSLn "reduce.compiled" 100 ("constructorForm = " ++ show cv) $
                 match' $ litFrame l $ cFrame $ catchAllFrame stack

              -- In case of a constructor, push the conFrame
              NotBlocked _ (Apply (Arg info (Con c vs))) -> performedSimplification $
                match' $ conFrame c vs $ catchAllFrame $ stack

              -- In case of a projection, push the litFrame
              NotBlocked _ (Proj p) -> performedSimplification $
                match' $ projFrame p $ stack

              -- Otherwise, we are stuck.  If we were stuck before,
              -- we keep the old reason, otherwise we give reason StuckOn here.
              NotBlocked blocked e -> no (NotBlocked $ stuckOn e blocked) es'

-- If we reach the empty stack, then pattern matching was incomplete
match' [] = {- new line here since __IMPOSSIBLE__ does not like the ' in match' -}
  caseMaybeM (asks envAppDef) __IMPOSSIBLE__ $ \ f -> do
    traceSLn "impossible" 10
      ("Incomplete pattern matching when applying " ++ show f)
      __IMPOSSIBLE__
