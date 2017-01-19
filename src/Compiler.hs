module Compiler where

import Malfunction.AST
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.Syntax.Position

translateTerm :: TTerm -> Term
translateTerm t = case t of
  TVar i            -> undefined
  TPrim tp          -> translatePrim tp
  TDef name         -> translateName name
  TApp t0 args      -> Mapply (translateTerm t0) (translateArgs args)
  TLam t0           -> undefined
  TLit lit          -> translateLit lit
  TCon name         -> undefined
  TLet t0 t1        -> undefined
  TCase i tp t0 alt -> undefined
  TUnit             -> undefined
  TSort             -> undefined
  TErased           -> undefined
  TError err        -> undefined

f0 :: TTerm -> Term
f0 = snd . f 0

tt = TApp (TLam (TLam (TVar 0))) [(TLam (TVar 0))]

f :: Int -> TTerm -> (Int, Term)
f l (TLam t) = (l' + 1, Mlambda [show l'] t')
  where (l', t') = f l t
f l (TVar i) = (l, Mint $ CInt i)
f l (TApp fun xs) = (l, Mapply fun' ts)
  where
    fun' = snd $ f l fun
    (l', ts) = unzip $ map (f l) xs


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

translateArgs :: Args -> [Term]
translateArgs = undefined
