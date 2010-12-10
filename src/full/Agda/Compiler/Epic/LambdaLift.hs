{-# OPTIONS_GHC -Wall #-}
-- | Lift lambda expressions to top level definitions (Epic does not support
--   lambdas).
module Agda.Compiler.Epic.LambdaLift where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Writer
import qualified Data.Set as S

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState

import Agda.TypeChecking.Monad.Base (MonadTCM)

-- | LL makes it possible to emit new functions when we encounter a lambda
type LL = WriterT [Fun]

-- | lambda lift all the functions
lambdaLift :: MonadTCM m => [Fun] -> Compile m [Fun]
lambdaLift fs = do
  concat <$> sequence
    [do (f', lifts) <- runWriterT (lambdaLiftFun f)
        return $ f' : lifts
    | f <- fs]

-- | λ lift a function, this is in a LL (Writer monad)
lambdaLiftFun :: MonadTCM m => Fun -> LL (Compile m) Fun
lambdaLiftFun (Fun i name c vs e) = Fun i name c vs <$> lambdaLiftExpr e
lambdaLiftFun f@(EpicFun _ _ _)   = return f

-- | λ lift an expression, put all the new definitions in the writer monad
lambdaLiftExpr :: MonadTCM m => Expr -> LL (Compile m) Expr
lambdaLiftExpr expr = case expr of
    Var _    -> return expr
    Lit _    -> return expr
    e1@(Lam _ _) -> do
      -- This is the only difficult case, get a group of lambda binders,
      -- lambda lift the body of it, and create a new supercombinator from
      -- this.
      let (vs, e2) = collectLam e1
      topBinding <- lift topBindings
      let vs' = filter (`S.notMember` topBinding) $ fv e1
      e3 <- lambdaLiftExpr e2
      name <- lift newName
      tell [Fun True name "lambda" (vs' ++ vs) e3]
      return $ apps name (map Var vs')
    Con c n es -> Con c n <$> mapM lambdaLiftExpr es
    App v es -> App v <$> mapM lambdaLiftExpr es
    Case e brs -> Case <$> lambdaLiftExpr e
                       <*> mapM (\br -> do lle <- lambdaLiftExpr $ brExpr br; return br {brExpr = lle}) brs
    If a b c   -> If <$> lambdaLiftExpr a <*> lambdaLiftExpr b <*> lambdaLiftExpr c
    Let v e e' -> Let v <$> lambdaLiftExpr e <*> lambdaLiftExpr e'
    Lazy e     -> Lazy <$> lambdaLiftExpr e
    UNIT       -> return UNIT
    IMPOSSIBLE -> return IMPOSSIBLE
  where
    -- | Collect all the variables in a group of lambdas
    collectLam :: Expr -> ([Var], Expr)
    collectLam (Lam v e) = let (vs, e') = collectLam e in (v:vs, e')
    collectLam e         = ([], e)
