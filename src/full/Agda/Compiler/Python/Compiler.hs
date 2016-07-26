{-# LANGUAGE CPP #-}
module Agda.Compiler.Python.Compiler where

import Agda.Compiler.Common
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Treeless as T
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Monad

import Agda.Compiler.Python.Lang        as Py
import Language.Python.Common.AST       as Py
import Language.Python.Common.Pretty    as Py
import Language.Python.Common.PrettyAST as Py

import Control.Monad.IO.Class (liftIO)
import Control.Monad

import Text.PrettyPrint

#include "undefined.h"
import Agda.Utils.Impossible


infixl 4 <$$>

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
f <$$> x = fmap (fmap f) x

compilerMain :: Interface -> TCM ()
compilerMain i = compile i

compile :: Interface -> TCM ()
compile i = do
    writeModule =<< definitions =<< curDefs

writeModule :: Py.Module () -> TCM ()
writeModule m = do
  liftIO . writeFile "module.py" . render $ Py.pretty m

closedTerm :: TTerm -> TCM ()
closedTerm _ = pure ()

-- | Extract Agda term to Haskell expression.
--   Erased arguments are extracted as @()@.
--   Types are extracted as @()@.
term :: T.TTerm -> TCM Py.Exp
term tm0 = case tm0 of
  T.TVar i -> undefined {- do
    x <- lookupIndex i <$> asks ccCxt
    return $ hsVarUQ x -}
  T.TApp (T.TDef f) ts -> undefined {- do
    used <- lift $ getCompiledArgUse f
    if any not used && length ts >= length used
      then do
        f <- lift $ HS.Var <$> xhqn "du" f  -- used stripped function
        f `apps` [ t | (t, True) <- zip ts $ used ++ repeat True ]
      else do
        t' <- term (T.TDef f)
        t' `apps` ts -}
  T.TApp t ts -> do
    t' <- term t
    t' `apps` ts
  T.TLam at -> undefined {- do
    (nm:_) <- asks ccNameSupply
    intros 1 $ \ [x] ->
      hsLambda [HS.PVar x] <$> term at -}
  T.TLet t1 t2 -> undefined {- do
    t1' <- term t1
    intros 1 $ \[x] -> do
      t2' <- term t2
      return $ hsLet x (hsCast t1') t2' -}

  T.TCase sc ct def alts -> undefined {- do
    sc' <- term (T.TVar sc)
    alts' <- traverse (alt sc) alts
    def' <- term def
    let defAlt = HS.Alt dummy HS.PWildCard (HS.UnGuardedRhs def') emptyBinds

    return $ HS.Case (hsCast sc') (alts' ++ [defAlt]) -}

  T.TLit l -> literal l
  T.TDef q -> undefined {- do
    HS.Var <$> (lift $ xhqn "d" q) -}
  T.TCon q -> undefined {- do
    kit <- lift coinductionKit
    if Just q == (nameOfSharp <$> kit)
      then HS.Var <$> lift (xhqn "d" q)
      else hsCast' . HS.Con <$> lift (conhqn q) -}
  T.TPrim p  -> return $ compilePrim p
  T.TUnit    -> return Py.unit_con {- return HS.unit_con -}
  T.TSort    -> return Py.unit_con {- return HS.unit_con -}
  T.TErased  -> return Py.unit_con
  T.TError e -> return $ case e of
    T.TUnreachable ->  rtmUnreachableError
  where
    apps t ts = do
      ts' <- mapM term ts
      return $ Py.Call t (flip Py.ArgExpr () <$> ts') ()

definitions :: Definitions -> TCM (Py.Module ())
definitions defs = do
  Py.Module <$> mapM (definition . snd) (sortDefs defs)

definition :: Definition -> TCM (Py.Statement ())
definition def = do
  return $ Py.Print False [Py.string_lit $ show def] False ()

rtmUnreachableError :: Py.Exp
rtmUnreachableError = error "rtmUnreachableError"

mazErasedName :: String
mazErasedName = "erased"

compilePrim :: T.TPrim -> Py.Exp
compilePrim s =
  case s of
    T.PQuot -> Py.op2lambda Py.Divide -- fakeExp "(Prelude.quot :: Integer -> Integer -> Integer)"
    T.PRem  -> Py.op2lambda Py.Modulo -- fakeExp "(Prelude.rem :: Integer -> Integer -> Integer)"
    T.PSub  -> Py.op2lambda Py.Divide -- fakeExp "((Prelude.-) :: Integer -> Integer -> Integer)"
    T.PAdd  -> Py.op2lambda Py.Plus     -- fakeExp "((Prelude.+) :: Integer -> Integer -> Integer)"
    T.PMul  -> Py.op2lambda Py.Multiply -- fakeExp "((Prelude.*) :: Integer -> Integer -> Integer)"
    T.PGeq  -> Py.op2lambda Py.GreaterThanEquals -- fakeExp "((Prelude.>=) :: Integer -> Integer -> Bool)"
    T.PLt   -> Py.op2lambda Py.LessThan -- fakeExp "((Prelude.<) :: Integer -> Integer -> Bool)"
    T.PEq   -> Py.op2lambda Py.Equality -- fakeExp "((Prelude.==) :: Integer -> Integer -> Bool)"
    T.PSeq  -> Py.None () -- ??? How to compile
    T.PIf   -> __IMPOSSIBLE__

fakeExp :: String -> Py.Exp
fakeExp n = undefined

literal :: Literal -> TCM Py.Exp
literal l = case l of
  LitNat    _ x -> return $ Py.int_lit x
  LitFloat  _ x -> return $ Py.Float  x (show x) ()
  LitChar   _ x -> return $ Py.Strings [[x]] ()
  LitQName  _ x -> return $ litqname x
  LitString _ s -> return $ Py.Strings [s] ()
  LitMeta{}     -> __IMPOSSIBLE__

-- FIXME: Qualified module name and normal function call
litqname :: QName -> Py.Exp
litqname x =
  Py.Call
    (Py.string_lit "QName")
    [Py.ArgExpr (Py.int_lit n) (), Py.ArgExpr (Py.int_lit m) ()]
    ()
  where
    NameId n m = nameId $ qnameName x

{-
https://hackage.haskell.org/package/language-python-0.5.3/docs/Language-Python-Common-AST.html#t:Statement
https://hackage.haskell.org/package/language-python-0.5.3/docs/Language-Python-Common-AST.html#t:Expr
-}
