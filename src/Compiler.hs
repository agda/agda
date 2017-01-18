module Compiler where

import Malfunction.AST
import Agda.Treeless

compileTerm :: TTerm -> Term
compileTerm t = case t of
  TVar i            -> Mint . CInt $ i
  TPrim tp          -> compilePrim tp
  TDef name         -> compileName name
  TApp t0 args      -> Mapply (compileTerm t0) (compileArgs args)
  TLam t0           -> undefined
  TLit lit          -> undefined
  TCon name         -> undefined
  TLet t0 t1        -> undefined
  TCase i tp t0 alt -> undefined
  TUnit             -> undefined
  TSort             -> undefined
  TErased           -> undefined
  TError err        -> undefined

compilePrim :: TPrim -> Term
compilePrim = undefined

compileName :: QName -> Term
compileName = undefined

compileArgs :: Args -> [Term]
compileArgs = undefined
