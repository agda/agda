{-# LANGUAGE CPP, PatternGuards #-}
module Agda.TypeChecking.CompiledClause.Match where

import Control.Applicative
import qualified Data.Map as Map
import Data.Traversable

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

matchCompiled :: CompiledClauses -> Args -> TCM (Reduced (Blocked Args) Term)
matchCompiled c args = match c args id []

type Stack = [(CompiledClauses, Args, Args -> Args)]

-- TODO: literal/constructor pattern conflict (for Nat)

match :: CompiledClauses -> Args -> (Args -> Args) -> Stack -> TCM (Reduced (Blocked Args) Term)
match Fail args patch stack = return $ NoReduction $ NotBlocked (patch args)
match (Done _ t) args _ _ =
  return $ YesReduction $ substs (reverse $ map unArg args) t
match (Case n bs) args patch stack = do
  let (args0, Arg h v, args1) = extractNthElement' n args
  w  <- unfoldCorecursion =<< reduceB v
  cv <- constructorForm $ ignoreBlocking w
  let v      = ignoreBlocking w
      args'  = args0 ++ [Arg h v] ++ args1
      stack' = maybe [] (\c -> [(c, args', patch)]) (catchAllBranch bs)
               ++ stack
      patchLit args = patch (args0 ++ [Arg h v] ++ args1)
        where (args0, args1) = splitAt n args
      patchCon c m args = patch (args0 ++ [Arg h $ Con c vs] ++ args1)
        where (args0, args1') = splitAt n args
              (vs, args1)     = splitAt m args1'
  case w of
    Blocked x _            -> return $ NoReduction $ Blocked x (patch args')
    NotBlocked (MetaV x _) -> return $ NoReduction $ Blocked x (patch args')
    NotBlocked (Lit l) -> case Map.lookup l (litBranches bs) of
      Nothing -> match' stack''
      Just cc -> match cc (args0 ++ args1) patchLit stack''
      where
        stack'' = (++ stack') $ case cv of
          Con c vs -> case Map.lookup c (conBranches bs) of
            Nothing -> []
            Just cc -> [(cc, args0 ++ vs ++ args1, patchCon c (length vs))]
          _        -> []
    NotBlocked (Con c vs) -> case Map.lookup c (conBranches bs) of
      Nothing -> match' stack'
      Just cc -> match cc (args0 ++ vs ++ args1) (patchCon c (length vs)) stack'
    NotBlocked _ -> return $ NoReduction $ NotBlocked (patch args')

match' :: Stack -> TCM (Reduced (Blocked Args) Term)
match' ((c, args, patch):stack) = match c args patch stack
match' [] = typeError $ GenericError "Incomplete pattern matching"

unfoldCorecursion (NotBlocked (Def f args)) =
  unfoldDefinition True reduceB (Def f []) f args
unfoldCorecursion w = return w

