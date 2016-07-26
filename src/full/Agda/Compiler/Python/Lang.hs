module Agda.Compiler.Python.Lang
  ( module Py
  , module Agda.Compiler.Python.Lang
  )
where

import Language.Python.Common.AST as Py

type Exp        = Py.Expr ()
type Statement_ = Py.Statement ()

unit_con :: Py.Expr ()
unit_con = Py.Tuple [] ()

int_lit :: Integer -> Py.Expr ()
int_lit x = Py.Int x (show x) ()

string_lit :: String -> Py.Expr ()
string_lit x = Py.Strings [x] ()

ident :: String -> Py.Ident ()
ident x = Py.Ident x ()

param :: Py.Ident () -> Py.Parameter ()
param i = Py.Param i Nothing Nothing ()

op2lambda :: (() -> Py.Op ()) -> Py.Expr ()
op2lambda op =
    Py.Lambda
        [param x, param y]
        (Py.BinaryOp (op ()) (Py.Var x ()) (Py.Var y ()) ()) ()
  where
    x = ident "x"
    y = ident "y"
