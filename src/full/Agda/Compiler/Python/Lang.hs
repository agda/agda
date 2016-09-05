module Agda.Compiler.Python.Lang
  ( module Py
  , module Agda.Compiler.Python.Lang
  )
where

import Data.Word
import Language.Python.Common.AST as Py

type Exp  = Py.Expr ()
type Stmt = Py.Statement ()

unit_con :: Py.Expr ()
unit_con = Py.Tuple [] ()

int_lit :: Integer -> Py.Expr ()
int_lit x = Py.Int x (show x) ()

word64_lit :: Word64 -> Py.Expr ()
word64_lit x = Py.Int (toInteger x) (show x) ()

string_lit :: String -> Py.Expr ()
string_lit x = Py.Strings [show x] ()

ident :: String -> Py.Ident ()
ident x = Py.Ident x ()

param :: Py.Ident () -> Py.Parameter ()
param i = Py.Param i Nothing Nothing ()

var :: String -> Py.Expr ()
var x = Py.Var (ident x) ()

op2lambda :: (() -> Py.Op ()) -> Py.Expr ()
op2lambda op =
    Py.Lambda
        [param x, param y]
        (Py.BinaryOp (op ()) (Py.Var x ()) (Py.Var y ()) ()) ()
  where
    x = ident "x"
    y = ident "y"

lambda :: [String] -> Py.Expr () -> Py.Expr ()
lambda ps body = Py.Lambda ((param . ident) <$> ps) body ()

(<.>) :: Py.Expr () -> Py.Ident () -> Py.Expr ()
f <.> m = Py.Dot f m ()

(<:=>) :: Py.Expr () -> Py.Expr () -> Py.Statement ()
p <:=> v = Py.Assign [p] v ()

(<@>) :: Py.Expr () -> Py.Expr () -> Py.Expr ()
e <@> s = Py.Subscript e s ()

type PythonCode = String
data PlainPython = PlainPython PythonCode
data MemberId = MemberId String
