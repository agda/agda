{-# OPTIONS -cpp #-}
module TypeChecking.With where

import Control.Applicative

import Syntax.Common
import Syntax.Internal
import Syntax.Abstract (LHS(..), RHS(..))
import qualified Syntax.Abstract as A

import TypeChecking.Monad
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.Primitive hiding (Nat)
import TypeChecking.Rules.LHS

import Utils.Permutation

#include "../undefined.h"

-- | Compute the clauses for the with-function given the original patterns.
buildWithFunction :: QName -> Telescope -> [Arg Pattern] -> Permutation -> Nat -> [A.Clause] -> TCM [A.Clause]
buildWithFunction aux gamma qs perm n cs = mapM buildWithClause cs
  where
    buildWithClause (A.Clause (LHS i _ ps wps) rhs wh) = do
      let (wps0, wps1) = splitAt n wps
          ps0          = map (Arg NotHidden . unnamed) wps0
      rhs <- buildRHS rhs
      ps  <- stripWithClausePatterns gamma qs perm ps
      return $ A.Clause (LHS i aux (ps ++ ps0) wps1) rhs wh

    buildRHS rhs@(RHS _)     = return rhs
    buildRHS rhs@AbsurdRHS   = return rhs
    buildRHS (WithRHS es cs) = WithRHS es <$> mapM buildWithClause cs

{-| @stripWithClausePatterns Γ qs π ps = ps'@

    @Δ@ - context bound by lhs of original function (not an argument)

    @Γ@ - type of arguments to original function

    @qs@ - internal patterns for original function

    @π@ - permutation taking @vars(qs)@ to @support(Δ)@

    @ps@ - patterns in with clause (presumably of type @Γ@)

    @ps'@ - patterns for with function (presumably of type @Δ@)
-}
stripWithClausePatterns :: Telescope -> [Arg Pattern] -> Permutation -> [NamedArg A.Pattern] -> TCM [NamedArg A.Pattern]
stripWithClausePatterns gamma qs perm ps = do
  psi <- insertImplicitPatterns ps gamma
  ps' <- strip gamma psi qs
  -- TODO: remember dot patterns
  return $ permute perm ps'
  where
    -- implicit args inserted at top level
    -- all three arguments should have the same size
    strip :: Telescope -> [NamedArg A.Pattern] -> [Arg Pattern] -> TCM [NamedArg A.Pattern]
    strip _           []      (_ : _) = __IMPOSSIBLE__
    strip _           (_ : _) []      = __IMPOSSIBLE__
    strip EmptyTel    (_ : _) _       = __IMPOSSIBLE__
    strip ExtendTel{} []      _       = __IMPOSSIBLE__
    strip EmptyTel    []      []      = return []
    strip (ExtendTel a tel) (p : ps) (q : qs) = case unArg q of
      VarP _  -> do
        underAbstraction a tel $ \tel -> strip tel ps qs
        return $ p : ps

      ConP c qs' -> case namedThing $ unArg p of
        A.ConP _ c' ps' | c == c' -> do

          -- The type is a datatype
          Def d us <- normalise $ unEl (unArg a)

          -- Compute the argument telescope for the constructor
          Con c []    <- constructorForm =<< normalise (Con c [])
          TelV tel' _ <- telView . flip apply us . defType <$> getConstInfo c

          -- Compute the new telescope
          let v     = Con c $ reverse [ Arg h (Var i []) | (i, Arg h _) <- zip [0..] $ reverse qs' ]
              tel'' = tel' `abstract` absApp tel v

          -- Insert implicit patterns
          psi' <- insertImplicitPatterns (ps' ++ ps) tel''

          -- Keep going
          strip tel'' psi' (qs' ++ qs)
        _ -> typeError $ WithClausePatternMismatch (namedThing $ unArg p) (unArg q)

      LitP lit -> case namedThing $ unArg p of
        A.LitP lit' | lit == lit' -> strip (tel `absApp` Lit lit) ps qs
        _ -> typeError $ WithClausePatternMismatch (namedThing $ unArg p) (unArg q)
          

