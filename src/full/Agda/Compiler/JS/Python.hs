{-# LANGUAGE CPP          #-}
{-# LANGUAGE TypeFamilies #-}
module Agda.Compiler.JS.Python
where

import Agda.Compiler.JS.Syntax as Syntax

import Agda.Compiler.Python.Lang ((<.>), (<:=>), (<@>))
import qualified Agda.Compiler.Python.Lang        as Py
import qualified Language.Python.Common.AST       as Py
import qualified Language.Python.Common.Pretty    as Py
import qualified Language.Python.Common.PrettyAST as Py

import Agda.Syntax.Common ( Nat )

#include "undefined.h"
import Agda.Utils.Impossible

import Data.List (intercalate)
import qualified Data.Map as Map (toList)
import Data.Set (Set)
import qualified Data.Set as Set (toList)
import Debug.Trace


-- * constants

exportsIdent :: Py.Ident ()
exportsIdent = Py.ident "exports"

exportsDict :: Py.Exp
exportsDict = Py.Var exportsIdent ()

pretty :: Nat -> Module -> String
pretty n m = Py.renderStyle style' . Py.pretty $ python n m
  where
    style' = Py.style {Py.lineLength = 80}

class Python p where
  type PyRep p :: *
  python :: Nat -> p -> PyRep p

instance Python Module where
  type PyRep Module = Py.Module ()
  python n (Module gid exps) =
    Py.Module (moduleInit (globals exps) (python n <$> exps))

{-
      js = toList (globals es)
      imports = unlines $
            ["var agdaRTS = require(\"agda-rts\");"] ++
            ["var " ++ pretty n (i+1) e ++ " = require(" ++ modname e ++ ");"
            | e <- js]-}

moduleInit :: Set GlobalId -> [Py.Stmt] -> [Py.Stmt]
moduleInit gs ps = imports ++ defineSelf ++ ps
  where
    imports =
      [ Py.Import [Py.ImportItem (Py.ident <$> ns) Nothing ()] ()
      | (GlobalId ns) <- Set.toList gs
      ]
    defineSelf =
      [ exportsDict <:=> Py.Dictionary [] ()
      ]


instance Python Export where
  type PyRep Export = Py.Stmt
  python n (Export (member:_) expr) =
    (exportsDict <@> (Py.string_lit $ unMemberId member))
    <:=>
    python n expr

  python n bad@(Export [] _) = error $ show bad

instance Python Exp where
  type PyRep Exp = Py.Exp
  python n (Self)                 = exportsDict
  python n (Local x)              = python n x
  python n (Global m)             = python n m
  python n (Undefined)            = Py.None () -- "undefined"
  python n (String s)             = Py.string_lit s -- TODO: Unescape!
  python n (Char c)               = __UNDEFINED__ -- "\"" ++ unescape c ++ "\""
  python n (Integer x)            = Py.int_lit x -- "agdaRTS.primIntegerFromString(\"" ++ show x ++ "\")"
  python n (Double x)             = __UNDEFINED__ -- show x
  python n (Lambda x e)           =
    Py.Lambda
      ((Py.param . localIdent (n+x) . LocalId) <$> [x-1, x-2 .. 0])
      (block (n+x) e)
      ()
{-
    "function (" ++
      intercalate ", " (pretties (n+x) i (map LocalId [x-1, x-2 .. 0])) ++
    ") " ++ block (n+x) i e
-}
  python n (Object o) | null o    = Py.Dictionary [] () -- "{}"
  python n (Object o) | otherwise =
    Py.Dictionary
      [ Py.DictMappingPair (memberIdToString member) (python n value)
        | (member, value) <- Map.toList o ]
      ()
  python n (Apply f es)           = -- python f ++ "(" ++ intercalate ", " (pretties n i es) ++ ")"
    Py.Call
      (python n f)
      ((\e -> Py.ArgExpr (python n e) ()) <$> es)
      ()
  -- function call
  python n (Lookup e l)           =
    case e of
      g@(Global _) -> (python n e <.> exportsIdent) <@> memberIdToString l
      g            -> python n e <@> memberIdToString l
  python n (If c t f)             = Py.CondExpr (python n c) (python n t) (python n f) ()
  python n (PreOp op e)           = Py.UnaryOp (Py.Not ()) (python n e) () -- TODO: Preop
  python n (BinOp e op f)         = __UNDEFINED__ -- "(" ++ python e ++ " " ++ op ++ " " ++ python f ++ ")"
  python n (Const c)              = __UNDEFINED__ -- c
  python n (PlainJS js)           = Py.lambda ["xtodo"] $ Py.string_lit js -- "(" ++ js ++ ")"

-- TODO: Nonrepresentable names are converted into a _uFFFF unicode representation
encodeUnicode :: String -> String
encodeUnicode = id

-- TODO
block :: Nat -> Exp -> Py.Exp
block n e = python n e

{-
RULES:
Exports are local functions to a module
Lookups are function calls from a qualfied module
Nonrepresentable names are converted into a _uFFFF unicode representation, using the module names

QUESION:
How to represents lambdas
 * Python lambda
 * Python local functions and call on the local function

OR:
Exports are part of a local dictionary
lookups are part of
-}

varName :: Nat -> Int -> String -> String
varName n x p = p ++ show (n - x - 1)

memberIdent :: Nat -> MemberId -> Py.Ident ()
memberIdent n (MemberId x) = Py.ident x

memberIdToString :: MemberId -> Py.Expr ()
memberIdToString (MemberId x) = Py.string_lit x

localIdent :: Nat -> LocalId -> Py.Ident ()
localIdent n (LocalId x) = Py.ident $ varName n x "lx"

instance Python LocalId where
  type PyRep LocalId = Py.Expr ()
  python n (LocalId x) = Py.var $ varName n x "lx"

instance Python GlobalId where
  type PyRep GlobalId = Py.Expr ()
  python n (GlobalId m) = Py.var $ intercalate "." m

instance Python MemberId where
  type PyRep MemberId = Py.Expr ()
  python n (MemberId member) = Py.var member

-- * helpers

unMemberId :: MemberId -> String
unMemberId (MemberId m) = m
