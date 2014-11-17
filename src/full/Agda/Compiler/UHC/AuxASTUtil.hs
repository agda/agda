module Agda.Compiler.UHC.AuxASTUtil
  ( bindExpr
  )
where


import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.Naming

-- | Bind an expression to a fresh variable name
bindExpr :: Monad m => Expr -> (HsName -> FreshNameT m Expr) -> FreshNameT m Expr
bindExpr expr f =
  case expr of
    Var v -> f v
    _     -> do
        v <- freshLocalName
        body <- f v
        return $ lett v expr body
                
