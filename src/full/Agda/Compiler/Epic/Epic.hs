{-# OPTIONS_GHC -Wall #-}
-- | Pretty-print the AuxAST to valid Epic code.
module Agda.Compiler.Epic.Epic 
  ( prettyEpicFun
  ) where

import Data.Char
import Data.List

#include "../../undefined.h"
import Agda.Utils.Impossible

import Agda.Compiler.Epic.AuxAST

-- * Some auxilliary pretty-printer functions
(<+>) :: String -> String -> String
x <+> y = x ++ " " ++ y
infixr 6 <+>

($$) :: String -> String -> String
x $$ y  = x ++ "\n" ++ y
infixr 5 $$

many :: [String] -> String
many vs = paren $ intercalate ", " vs

paren :: String -> String
paren s = "(" <+> s <+> ")"

curly :: String -> String
curly s = "{-" <+> s <+> "-}"

-- * Pretty-printer
-- | Print a function to an Epic string
prettyEpicFun :: Fun -> String
prettyEpicFun (Fun inline name comment vars e) =
    "--" <+> comment $$ 
    (if inline then "%inline " else "") ++ name 
    <+> many (map typVar vars) <+> "-> Any" <+> "=" <+> prettyEpic e
prettyEpicFun (EpicFun name comment def) = 
    "--" <+> comment $$ 
    "%inline" <+> name <+> def

-- | Print expression to Epic expression
prettyEpic :: Expr -> String
prettyEpic expr = case expr of
    Var v -> v
    Lit l -> prettyEpicLit l
    Lam _ _ -> __IMPOSSIBLE__ -- We have lambda lifted away all λs
    Con t q args -> curly (show q) <+> paren ("Con" <+> show t <+> many (map prettyEpic args))
    If a b c -> "if" <+> prettyEpic a <+> "then" <+> prettyEpic b <+> "else" <+> prettyEpic c
    Let v e e' -> "let" <+> typVar v <+> "=" <+> prettyEpic e <+> "in" <+> prettyEpic e' 
    App v es -> v <+> many (map prettyEpic es)
    Case e brs -> "case" <+> prettyEpic e <+> "of {"
               <+> intercalate "\n | " (map prettyEpicBr brs) <+> "}"
    Lazy e -> "lazy" <+> paren (prettyEpic e)
    UNIT -> "unit"
    IMPOSSIBLE -> "impossible"
    
prettyEpicBr :: Branch -> String
prettyEpicBr br = case br of
    Branch c q vs e ->
       curly (show q)  <+> 
       "Con" <+> show c 
       <+> many (map typVar vs)
       <+> "->" <+> prettyEpic e
    BrInt n e       ->  show n <+> "->" <+> prettyEpic e
    Default e       -> "Default ->" <+> prettyEpic e

prettyEpicLit :: Lit -> String
prettyEpicLit l = case l of
    LInt n    -> show n ++ "L"
    LChar c   -> show (ord c)
    LString s -> show s

typVar :: Var -> String
typVar v = v <+> ":" <+> "Any"
