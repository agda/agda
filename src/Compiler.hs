{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Compiler (translate) where

import Data.Char

import Malfunction.AST
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Control.Monad
import Control.Monad.State

type MonadTranslate = MonadState Int

translate :: TTerm -> Term
translate t = translateTerm t `evalState` 0

translateTerm :: MonadTranslate m => TTerm -> m Term
translateTerm t = case t of
  TVar i            -> return . identToVarTerm $ i
  TPrim tp          -> return $ translatePrim tp
  TDef name         -> return $ translateName name
  TApp t0 args      -> translateApp t0 args
  TLam t0           -> translateLam t0
  TLit lit          -> return $ translateLit lit
  TCon name         -> undefined
  TLet t0 t1        -> liftM2 Mlet (pure <$> translateBinding t0) (translateTerm t1)
  -- @def@ is the default value if all @alt@s fail.
--  TCase i tp def alt -> liftM2 Mswitch (translateTerm def) (mapM translateSwitch alt)
  TCase i tp def alt -> do
    let t = identToVarTerm i
    d <- translateTerm def
    cs <- mapM translateSwitch alt
    return $ Mswitch t (cs ++ pure (anything, d))
    where
      anything :: [Case]
      anything = [Intrange (minBound, maxBound) , Deftag]
  TUnit             -> error "Unimplemented"
  TSort             -> error "Unimplemented"
  TErased           -> error "Unimplemented"
  TError err        -> error "Unimplemented"

identToVarTerm :: Int -> Term
identToVarTerm = Mvar . ident

translateSwitch :: MonadTranslate m => TAlt -> m ([Case], Term)
translateSwitch alt = case alt of
--  TAGuard c t -> liftM2 (,) (pure <$> translateCase c) (translateTerm t)
  TALit pat body -> do
    b <- translateTerm body
    let c = pure $ litToCase pat
    return (c, b)
  _              -> error "Unimplemented"

litToCase :: Literal -> Case
litToCase l = case l of
  LitNat _ i -> let i' = fromInteger i in Intrange (i', i')
  _          -> error "Unimplemented"

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
      xs = mapM translateTerm xst `evalState` i
  return $ Mapply f xs

incr :: MonadTranslate m => m ()
incr = modify succ

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
