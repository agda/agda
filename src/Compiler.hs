{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Compiler where

import Data.Char

import Malfunction.AST
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Control.Monad
import Control.Monad.State

type Translate = State Int
type MonadTranslate = MonadState Int

translateTerm :: MonadTranslate m => TTerm -> m Term
translateTerm t = case t of
  TVar i            -> return . Mvar . ident $ i
  TPrim tp          -> return $ translatePrim tp
  TDef name         -> return $ translateName name
  TApp t0 args      -> translateApp t0 args
  TLam t0           -> translateLam t0
  TLit lit          -> return $ translateLit lit
  TCon name         -> undefined
  TLet t0 t1        -> liftM2 Mlet (pure <$> translateBinding t0) (translateTerm t1)
  TCase i tp t0 alt -> liftM2 Mswitch (translateTerm t0) (mapM translateSwitch alt)
  TUnit             -> undefined
  TSort             -> undefined
  TErased           -> undefined
  TError err        -> undefined

translateSwitch :: MonadTranslate m => TAlt -> m ([Case], Term)
translateSwitch alt = case alt of
  TAGuard c t -> liftM2 (,) (pure <$> translateCase c) (translateTerm t)
  _           ->  error "Not implemented"

translateCase :: MonadTranslate m => TTerm -> m Case
-- oh-oh! might be tricky to translate a general term to a "guard" in mlf.
translateCase = error "Not implemented"

translateBinding :: MonadTranslate m => TTerm -> m Binding
translateBinding t = Unnamed <$> translateTerm t

translateLam :: MonadTranslate m => TTerm -> m Term
translateLam lam = do
  t <- translateTerm lam
  i <- ident <$> get
  incr
  return (Mlambda [i] t)

translateApp :: MonadTranslate m => TTerm -> [TTerm] -> m Term
translateApp ft xst = do
  i <- get
  let f  = translateTerm ft       `evalState` i
  let xs = mapM translateTerm xst `evalState` i
  return $ Mapply f xs

incr :: MonadTranslate m => m ()
incr = modify succ

decr :: MonadTranslate m => m ()
decr = modify pred

ident :: Int -> String
ident i = "v" ++ show i

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
