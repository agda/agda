module Agda.Compiler.JS.Pretty where

import Prelude hiding ( null )
import Data.List ( intercalate )
import Data.Set ( Set, toList, singleton, insert, member )
import Data.Map ( Map, toAscList, empty, null )

import Agda.Syntax.Common ( Nat )

import Agda.Compiler.JS.Syntax
  ( Exp(Self,Local,Global,Undefined,String,Char,Integer,Double,Lambda,Object,Apply,Lookup,If,BinOp,PreOp,Const),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId), Module(Module), Export(Export),
    globals )

-- Pretty-print a lambda-calculus expression as ECMAScript.

-- Since ECMAScript is C-like rather than Haskell-like, it's easier to
-- do the pretty-printing directly than use the Pretty library, which
-- assumes Haskell-like indentation.

br :: Int -> String
br i = "\n" ++ take (2*i) (repeat ' ')

unescape :: Char -> String
unescape '"'      = "\\\""
unescape '\\'     = "\\\\"
unescape '\n'     = "\\n"
unescape '\r'     = "\\r"
unescape '\x2028' = "\\u2028"
unescape '\x2029' = "\\u2029"
unescape c        = [c]

unescapes :: String -> String
unescapes s = concat (map unescape s)

-- pretty n i e pretty-prints e, under n levels of de Bruijn binding,
-- with i levels of indentation.

class Pretty a where
    pretty :: Nat -> Int -> a -> String

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty n i (x,y) = pretty n i x ++ ": " ++ pretty n (i+1) y

-- Pretty-print collections

class Pretties a where
    pretties :: Nat -> Int -> a -> [String]

instance Pretty a => Pretties [a] where
  pretties n i = map (pretty n i)

instance (Pretty a, Pretty b) => Pretties (Map a b) where
  pretties n i o = pretties n i (toAscList o)

-- Pretty print identifiers

instance Pretty LocalId where
  pretty n i (LocalId x) = "x" ++ show (n - x - 1)

instance Pretty GlobalId where
  pretty n i (GlobalId m) = intercalate "_" m

instance Pretty MemberId where
  pretty n i (MemberId s) = "\"" ++ unescapes s ++ "\""

-- Pretty print expressions

instance Pretty Exp where
  pretty n i (Self)                 = "exports"
  pretty n i (Local x)              = pretty n i x
  pretty n i (Global m)             = pretty n i m
  pretty n i (Undefined)            = "undefined"
  pretty n i (String s)             = "\"" ++ unescapes s ++ "\""
  pretty n i (Char c)               = "\"" ++ unescape c ++ "\""
  pretty n i (Integer x)            = show x
  pretty n i (Double x)             = show x
  pretty n i (Lambda x e)           =
    "function (" ++
      intercalate ", " (pretties (n+x) i (map LocalId [x-1, x-2 .. 0])) ++
    ") " ++ block (n+x) i e
  pretty n i (Object o) | null o    = "{}"
  pretty n i (Object o) | otherwise =
    "{" ++ br (i+1) ++ intercalate ("," ++ br (i+1)) (pretties n i o) ++ br i ++ "}"
  pretty n i (Apply f es)           = pretty n i f ++ "(" ++ intercalate ", " (pretties n i es) ++ ")"
  pretty n i (Lookup e l)           = pretty n i e ++ "[" ++ pretty n i l ++ "]"
  pretty n i (If e f g)             =
    "(" ++ pretty n i e ++ "? " ++ pretty n i f ++ ": " ++ pretty n i g ++ ")"
  pretty n i (PreOp op e)           = "(" ++ op ++ " " ++ pretty n i e ++ ")"
  pretty n i (BinOp e op f)         = "(" ++ pretty n i e ++ " " ++ op ++ " " ++ pretty n i f ++ ")"
  pretty n i (Const c)              = c

block :: Nat -> Int -> Exp -> String
block n i (If e f g) = "{" ++ br (i+1) ++ block' n (i+1) (If e f g) ++ br i ++ "}"
block n i e          = "{" ++ br (i+1) ++ "return " ++ pretty n (i+1) e ++ ";" ++ br i ++ "}"

block' :: Nat -> Int -> Exp -> String
block' n i (If e f g) = "if (" ++ pretty n i e ++ ") " ++ block n i f ++ " else " ++ block' n i g
block' n i e          = block n i e

modname :: GlobalId -> String
modname (GlobalId ms) = "\"" ++ intercalate "." ms ++ "\""

exports :: Nat -> Int -> Set [MemberId] -> [Export] -> String
exports n i lss [] = ""
exports n i lss (Export ls e : es) | member (init ls) lss =
  "exports[" ++ intercalate "][" (pretties n i ls) ++ "] = " ++ pretty n (i+1) e ++ ";" ++ br i ++
  exports n i (insert ls lss) es
exports n i lss (Export ls e : es) | otherwise =
  exports n i lss (Export (init ls) (Object empty) : Export ls e : es)

instance Pretty Module where
  pretty n i (Module m es) =
    "define([" ++ intercalate "," ("\"exports\"" : map modname js) ++ "]," ++
    "function(" ++ intercalate "," ("exports" : pretties n i js) ++ ") {" ++ br (i+1) ++
    exports n (i+1) (singleton []) es ++
    "});" ++ br i
      where js = toList (globals es)
