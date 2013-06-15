{-# LANGUAGE CPP, PatternGuards #-}
module Agda.TypeChecking.CompiledClause.Match where

import Control.Applicative
import Control.Monad.Reader (asks)
import qualified Data.Map as Map
import Data.Traversable
import Data.List

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive

import Agda.Utils.List

import Agda.Utils.Impossible
#include "../../undefined.h"

matchCompiled :: CompiledClauses -> MaybeReducedArgs -> TCM (Reduced (Blocked Args) Term)
matchCompiled c args = match' [(c, args, id)]

-- | A stack entry is a triple consisting of
--   1. the part of the case tree to continue matching,
--   2. the current argument vector, and
--   3. a patch function taking the current argument vector back
--      to the original argument vector.
type Frame = (CompiledClauses, MaybeReducedArgs, Args -> Args)
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

match' :: Stack -> TCM (Reduced (Blocked Args) Term)
match' ((c, args, patch) : stack) = do
  let no          args = return $ NoReduction $ NotBlocked $ patch $ map ignoreReduced args
      noBlocked x args = return $ NoReduction $ Blocked x  $ patch $ map ignoreReduced args
      yes t            = flip YesReduction t <$> asks envSimplification
  case c of

    -- impossible case
    Fail -> no args

    -- done matching
    Done xs t
      -- if the function was partially applied, return a lambda
      | m < n     -> yes $ applySubst (toSubst args) $ foldr lam t (drop m xs)
      -- otherwise, just apply instantiation to body
      -- apply the result to any extra arguments
      | otherwise -> yes $ applySubst (toSubst args0) t `apply` map ignoreReduced args1
      where
        n              = length xs
        m              = length args
        toSubst        = parallelS . reverse . map (unArg . ignoreReduced)
        (args0, args1) = splitAt n $ map (fmap $ fmap shared) args
        lam x t        = Lam (argInfo x) (Abs (unArg x) t)

    -- splitting on the @n@th argument
    Case n bs -> do
      case genericSplitAt n args of
        -- if the @n@th argument is not supplied, no match
        (_, []) -> no args
        -- if the @n@th argument is @v0@
        (args0, MaybeRed red (Arg info v0) : args1) -> do
          -- get the reduced form of @v0@
          w  <- case red of
                  Reduced b  -> return $ v0 <$ b
                  NotReduced -> unfoldCorecursion v0
          let v = ignoreBlocking w
              -- replace the @n@th argument by its reduced form
              args'  = args0 ++ [MaybeRed red $ Arg info v] ++ args1
              -- if a catch-all clause exists, put it on the stack
              stack' = maybe stack (\c -> (c, args', patch) : stack) (catchAllBranch bs)
              -- If our argument is @Lit l@, we push @litFrame l@ onto the stack.
              litFrame l stack =
                case Map.lookup l (litBranches bs) of
                  Nothing -> stack
                  Just cc -> (cc, args0 ++ args1, patchLit) : stack
              -- If our argument (or its constructor form) is @Con c vs@
              -- we push @conFrame c vs@ onto the stack.
              conFrame c vs stack =
                case Map.lookup (conName c) (conBranches bs) of
                    Nothing -> stack
                    Just cc -> ( content cc
                               , args0 ++ map (MaybeRed red) vs ++ args1
                               , patchCon c (length vs)
                               ) : stack
              -- The new patch function restores the @n@th argument to @v@:
              -- In case we matched a literal, just put @v@ back.
              patchLit args = patch (args0 ++ [Arg info v] ++ args1)
                where (args0, args1) = splitAt n args
              -- In case we matched constructor @c@ with @m@ arguments,
              -- contract these @m@ arguments @vs@ to @Con c vs@.
              patchCon c m args = patch (args0 ++ [Arg info $ Con c vs] ++ args1)
                where (args0, args1') = splitAt n args
                      (vs, args1)     = splitAt m args1'

          -- Now do the matching on the @n@ths argument:
          case ignoreSharing <$> w of
            Blocked x _            -> noBlocked x args'
            NotBlocked (MetaV x _) -> noBlocked x args'

            -- In case of a literal, try also its constructor form
            NotBlocked (Lit l) -> performedSimplification $ do
              cv <- constructorForm v
              let cFrame stack = case ignoreSharing cv of
                    Con c vs -> conFrame c vs stack
                    _        -> stack
              match' $ litFrame l $ cFrame stack'

            -- In case of a constructor, push the conFrame
            NotBlocked (Con c vs) -> performedSimplification $
              match' $ conFrame c vs $ stack'

            NotBlocked _ -> no args'

-- If we reach the empty stack, then pattern matching was incomplete
match' [] = do
  mf <- asks envAppDef
  flip (maybe __IMPOSSIBLE__) mf $ \ f -> do
    typeError $ GenericError $ "Incomplete pattern matching when applying " ++ show f


-- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
-- need also to instantiate metas, see Issue 826.
unfoldCorecursion v = do
  v <- instantiate v
  case v of
    Def f args -> unfoldDefinition True unfoldCorecursion (Def f []) f args
    Shared{}   -> fmap shared <$> unfoldCorecursion (ignoreSharing v) -- don't update when unfolding corecursion!
    _          -> reduceB v
