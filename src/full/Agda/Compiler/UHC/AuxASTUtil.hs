{-# LANGUAGE CPP #-}
-- has it's own module to break dependency loop
module Agda.Compiler.UHC.AuxASTUtil
  ( bindExpr
  , ctagCtorName
  )
where

import Agda.Compiler.UHC.Bridge
import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.Naming

#include "undefined.h"
import Agda.Utils.Impossible

-- | Bind an expression to a fresh variable name
bindExpr :: Monad m => Expr -> (HsName -> FreshNameT m Expr) -> FreshNameT m Expr
bindExpr expr f =
  case expr of
    Var v -> f v
    _     -> do
        v <- freshLocalName
        body <- f v
        return $ lett v expr body

ctagCtorName :: CTag -> HsName
ctagCtorName = destructCTag __IMPOSSIBLE__ (\_ x _ _ -> x)
