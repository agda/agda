{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Compiler (translate, Term) where

import Data.Char

import Malfunction.AST
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Common (NameId)

import Control.Monad
import Control.Monad.State

type MonadTranslate = MonadState Int

translate :: TTerm -> Term
translate t = translateTerm t `evalState` 0

translateTerm :: MonadTranslate m => TTerm -> m Term
translateTerm tt = case tt of
  TVar i            -> return . identToVarTerm $ i
  TPrim tp          -> return $ translatePrim tp
  TDef name         -> translateName name
  TApp t0 args      -> translateApp t0 args
  TLam t0           -> translateLam t0
  TLit lit          -> return $ translateLit lit
  -- TODO: Translate constructors differently from names.
  -- Don't know if we should do the same when translating TDef's, but here we
  -- should most likely use malfunction "tags" to represent constructors
  -- in an "untyped but injective way". That is, we only care that each
  -- constructor maps to a unique number such that we will be able to
  -- distinguish it in malfunction.
  TCon name         -> translateName name
  TLet t0 t1        -> liftM2 Mlet (pure <$> translateBinding t0) (translateTerm t1)
  -- @def@ is the default value if all @alt@s fail.
--  TCase i tp def alt -> liftM2 Mswitch (translateTerm def) (mapM translateSwitch alt)
  TCase i _ def alt -> do
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
  TError err        -> error $ "Error: " ++ show err

identToVarTerm :: Int -> Term
identToVarTerm = Mvar . ident

translateSwitch :: MonadTranslate m => TAlt -> m ([Case], Term)
translateSwitch alt = case alt of
--  TAGuard c t -> liftM2 (,) (pure <$> translateCase c) (translateTerm t)
  TALit pat body -> do
    b <- translateTerm body
    let c = pure $ litToCase pat
    return (c, b)
  -- TODO: Stub!
  TACon{}        -> return ([], Mvar "TACon")
  TAGuard{}      -> return ([], Mvar "TAGuard")

litToCase :: Literal -> Case
litToCase l = case l of
  LitNat _ i -> CaseInt . fromInteger $ i
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

-- TODO: Needs to be passed terms as well.
-- To fix this we need to "lookahead" when translating `TApp`
-- Alternatively we can do so that this:
--   TPrim PAdd
-- Translates to this:
--   lambda a b (+ a b)
-- This is what I've done below, it's a bit ugly but it should work.
-- Please note that the length of the array obviously needs
-- to be adjusted depending on it it's a Mintop1 or Mintop2.
translatePrim :: TPrim -> Term
translatePrim tp = Mlambda [varN, varM] $ case tp of
  PAdd -> op2 Add
  PSub -> op2 Sub
  PMul -> op2 Mul
  PQuot -> wrong
  PRem -> op2 Mo
  PGeq -> op2 Gt
  PLt -> wrong
  PEqI -> wrong
  PEqF -> wrong
  PEqS -> wrong
  PEqC -> wrong
  PEqQ -> wrong
  PIf -> wrong
  PSeq -> wrong
  where
    op2 t = Mintop2 t aType (Mvar varN) (Mvar varM)
    aType = TInt
    varN  = "n"
    varM  = "m"
    wrong = op2 Xor

translateName :: MonadTranslate m => QName -> m Term
translateName = aux . nameId . qnameName
  where
    -- I know this is a sort of dicy variable name to pick but for now I'll
    -- leave it here. It makes debugging slightly easier.
    aux :: MonadTranslate m => NameId -> m Term
    aux = return . Mvar . ("agda://" ++) . show

