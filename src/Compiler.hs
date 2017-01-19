module Compiler where

import Data.Char

import Malfunction.AST
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Control.Monad.State

type Translate = State Int

translateTerm :: TTerm -> Translate Term
translateTerm t = case t of
  TVar i            -> return . Mvar . ident $ i
  TPrim tp          -> return $ translatePrim tp
  TDef name         -> return $ translateName name
  TApp t0 args      -> translateApp t0 args
  TLam t0           -> translateLam t0
  TLit lit          -> return $ translateLit lit
  TCon name         -> undefined
  TLet t0 t1        -> undefined
  TCase i tp t0 alt -> undefined
  TUnit             -> undefined
  TSort             -> undefined
  TErased           -> undefined
  TError err        -> undefined


translateLam :: TTerm -> Translate Term
translateLam lam = do
  t <- translateTerm lam
  i <- ident <$> get
  incr
  return (Mlambda [i] t)

translateApp :: TTerm -> [TTerm] -> Translate Term
translateApp ft xst = do
  i <- get
  let f  = translateTerm ft       `evalState` i
  let xs = mapM translateTerm xst `evalState` i
  return $ Mapply f xs

incr :: Translate ()
incr = modify succ

decr :: Translate ()
decr = modify pred

-- Alphabet only has 26 unqiue values.
ident i = pure $ chr (i + ord 'a')

translateLit :: Literal -> Term
translateLit l = case l of
  LitNat _ x -> Mint (CInt (fromInteger x))
  LitString _ s -> Mstring s
  _ -> error "unsupported literal type"

translatePrim :: TPrim -> Term
translatePrim tp = Mglobal $ case tp of
  PAdd -> undefined
  PSub -> undefined
  PMul -> undefined
  PQuot -> undefined
  PRem -> undefined
  PGeq -> undefined
  PLt -> undefined
  PEqI -> undefined
  PEqF -> undefined
  PEqS -> undefined
  PEqC -> undefined
  PEqQ -> undefined
  PIf -> undefined
  PSeq -> undefined

translateName :: QName -> Term
translateName = undefined
