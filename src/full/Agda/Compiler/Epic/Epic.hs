{-# LANGUAGE CPP #-}

-- | Pretty-print the AuxAST to valid Epic code.
module Agda.Compiler.Epic.Epic
  ( prettyEpicFun
  , prettyEpic
  ) where

import Control.Monad.State

import Data.Char
import Data.List

import Data.Map (Map)
import qualified Data.Map as M

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce

#include "../../undefined.h"
import Agda.Utils.Impossible


import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Interface

-- * Some auxilliary pretty-printer functions
(<+>) :: String -> String -> String
x <+> y = x ++ " " ++ y
infixr 6 <+>

($$) :: String -> String -> String
x $$ y  = x ++ "\n" ++ y
infixr 5 $$

many :: [String] -> String
many vs = paren $ intercalate ", " vs

many' :: [String] -> String
many' [] = ""
many' vs = paren $ intercalate ", " vs

paren :: String -> String
paren s = "(" <+> s <+> ")"

curly :: String -> String
curly s = "{-" <+> s <+> "-}"

-- * Pretty-printer
-- | Print a function to an Epic string
prettyEpicFun :: MonadTCM m => Fun -> Compile m String
prettyEpicFun (Fun inline name mqname comment vars e) = do
    {-
    defs <- lift (gets (sigDefinitions . stImports))
    typ <- case mqname >>= flip M.lookup defs of
      Nothing -> return "-"
      Just def -> do
        doc <- lift $ prettyTCM =<< normalise (defType def)
        return $ show doc
    -}
    return $
      "--" <+> comment $$
      -- unlines (map ("-- " <+>) (lines typ)) $$
      (if inline then "%inline " else "") ++ name
        <+> many (map typVar vars) <+> "-> Any" <+> "=" <+> prettyEpic e

prettyEpicFun (EpicFun name _mqname comment def) = return $
    "--" <+> comment $$
    {-"%inline" <+> -} name <+> def

-- | Print expression to Epic expression
prettyEpic :: Expr -> String
prettyEpic expr = case expr of
    Var v -> v
    Lit l -> prettyEpicLit l
    Lam x e -> paren $ "\\" <+> typVar x <+> "." <+> paren (prettyEpic e)-- __IMPOSSIBLE__ -- We have lambda lifted away all λs
    Con (Tag t) q args -> curly (show q) <+> paren ("Con" <+> show t <+> many (map prettyEpic args))
    If a b c -> "if" <+> prettyEpic a <+> "then" <+> prettyEpic b <+> "else" <+> prettyEpic c
    Let v e e' -> "let" <+> typVar v <+> "=" <+> prettyEpic (id e) <+> "in" <+> prettyEpic e'
    App "proj" (Lit (LInt n) : e : es) -> paren (prettyEpic e <+> "!" <+> show n) <+> many' (map prettyEpic es)
    App v es -> v <+> many' (map (prettyEpic . id) es)
    Case e brs -> "case" <+> prettyEpic e <+> "of {"
               <+> intercalate "\n | " (map prettyEpicBr brs) <+> "}"
    Lazy e -> "lazy" <+> paren (prettyEpic e)
    UNIT -> "unit"
    IMPOSSIBLE -> "impossible"
    _ -> __IMPOSSIBLE__

prettyEpicBr :: Branch -> String
prettyEpicBr br = case br of
    Branch (Tag c) q vs e ->
       curly (show q)  <+>
       "Con" <+> show c
       <+> many (map typVar vs)
       <+> "->" <+> prettyEpic e
    BrInt n e       ->  show n <+> "->" <+> prettyEpic e
    Default e       -> "Default ->" <+> prettyEpic e
    _ -> __IMPOSSIBLE__

prettyEpicLit :: Lit -> String
prettyEpicLit l = case l of
    LInt n    -> show n ++ "L"
    LChar c   -> show (ord c)
    LString s -> show s
    LFloat f  -> show f

typVar :: Var -> String
typVar v = v <+> ":" <+> "Any"
