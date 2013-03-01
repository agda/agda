-- | Remove forced arguments from constructors.
{-# LANGUAGE CPP #-}
module Agda.Compiler.Epic.ForceConstrs where

import Control.Applicative
import Control.Monad.Trans

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Interface

import qualified Agda.Syntax.Common   as S
import qualified Agda.Syntax.Internal as T
import Agda.TypeChecking.Monad (TCM, reportSDoc)
import Agda.TypeChecking.Pretty

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Check which arguments are forced
makeForcedArgs :: T.Type -> ForcedArgs
makeForcedArgs (T.El _ term) = case term of
    T.Pi  arg ab  -> isRel arg : makeForcedArgs (T.unAbs ab)
    _ -> []
  where
    isRel :: T.Dom T.Type -> Forced
    isRel arg = case S.getRelevance arg of
      S.Relevant   -> NotForced
      S.Irrelevant -> Forced
      S.UnusedArg  -> Forced
      S.NonStrict  -> Forced -- can never be executed
      S.Forced     -> Forced -- It can be inferred

-- | Remove forced arguments from constructors and branches
forceConstrs :: [Fun] -> Compile TCM [Fun]
forceConstrs fs = mapM forceFun fs

forceFun :: Fun -> Compile TCM Fun
forceFun e@(EpicFun{}) = return e
forceFun (Fun inline name qname comment args expr) =
    Fun inline name qname comment args <$> forceExpr expr
  where
    -- | Remove all arguments to constructors that we don't need to store in an
    --   expression.
    forceExpr :: Expr -> Compile TCM Expr
    forceExpr expr = case expr of
        Var v        -> return $ Var v
        Lit l        -> return $ Lit l
        Lam v e      -> Lam v <$> forceExpr e
        Con tag q es -> do
            -- We only need to apply the non-forced arguments
            forcArgs <- getForcedArgs q
            return $ Con tag q $ notForced forcArgs es
        App v es     -> App v <$> mapM forceExpr es
        Case e bs    -> Case <$> forceExpr e <*> mapM forceBranch bs
        Let v e e'   -> lett v <$> forceExpr e <*> forceExpr e'
        If a b c     -> If <$> forceExpr a <*> forceExpr b <*> forceExpr c
        Lazy e       -> Lazy <$> forceExpr e
        UNIT         -> return expr
        IMPOSSIBLE   -> return expr

    -- | Remove all the arguments that don't need to be stored in the constructor
    --   For the branch
    forceBranch :: Branch -> Compile TCM Branch
    forceBranch br = case br of
        Branch  tag name vars e -> do
            ir <- getForcedArgs name
            let vs = notForced ir vars
                subs = forced ir vars

            e'' <- if all (`notElem` fv e) subs
                  then return e
                  else __IMPOSSIBLE__ -- If so, the removal of forced args has gone wrong
            Branch tag name vs <$> forceExpr e''
        BrInt i e -> BrInt i <$> forceExpr e
        Default e -> Default <$> forceExpr e
