-- | Remove forced (irrelevant) arguments from constructors.
module Agda.Compiler.Epic.ConstructorIrrelevancy where

import Control.Applicative

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState

import Agda.Syntax.Common
import qualified Agda.Syntax.Internal as T
import Agda.TypeChecking.Monad.Base (MonadTCM)


-- | Check which arguments are forced and create an IrrFilter
irrFilter :: T.Type -> IrrFilter
irrFilter (T.El _ term) = case term of
    T.Pi  arg ab  -> isRel arg : irrFilter (T.absBody ab)
    T.Fun arg typ -> isRel arg : irrFilter typ
    _ -> []
  where
    isRel :: Arg T.Type -> Bool
    isRel arg = case argRelevance arg of
      Relevant   -> True
      Irrelevant -> False
      Forced     -> False -- It can be inferred

-- | Remove irrelevant arguments from constructors and branches
constrIrr :: MonadTCM m => [Fun] -> Compile m [Fun]
constrIrr fs = mapM irrFun fs

irrFun :: MonadTCM m => Fun -> Compile m Fun
irrFun (Fun inline name comment args expr) =
    Fun inline name comment args <$> irrExpr expr
irrFun e@(EpicFun{}) = return e

-- | Remove all arguments to constructors that we don't need to store in an
--   expression.
irrExpr :: MonadTCM m => Expr -> Compile m Expr
irrExpr expr = case expr of
    Var v        -> return $ Var v
    Lit l        -> return $ Lit l
    Lam v e      -> Lam v <$> irrExpr e
    Con tag q es -> do
        -- We only need to apply the relevant arguments
        irrFilt <- getIrrFilter q
        return $ Con tag q $ pairwiseFilter irrFilt es
    App v es     -> App v <$> mapM irrExpr es
    Case e bs    -> Case <$> irrExpr e <*> mapM irrBranch bs
    Let v e e'   -> Let v <$> irrExpr e <*> irrExpr e'
    If a b c     -> If <$> irrExpr a <*> irrExpr b <*> irrExpr c
    Lazy e       -> Lazy <$> irrExpr e
    UNIT         -> return expr
    IMPOSSIBLE   -> return expr

-- | Remove all the arguments that doesn't need to be stored in the constructor
--   For the branch
irrBranch :: MonadTCM m => Branch -> Compile m Branch
irrBranch br = case br of
    Branch  tag name vars e -> do
        ir <- getIrrFilter name
        let vs = pairwiseFilter ir vars
            -- The removed arguments are substituted for unit
            subs = pairwiseFilter (map not ir) vars
            e'   = foldr (\x ex -> subst x "primUnit" ex) e subs
        Branch tag name vs <$> irrExpr e'
    BrInt i e -> BrInt i <$> irrExpr e
    Default e -> Default <$> irrExpr e
