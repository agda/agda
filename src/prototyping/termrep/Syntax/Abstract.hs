
module Syntax.Abstract where

type Name = String

data Decl = Def Name Expr Expr
          | Ax  Name Expr
  deriving (Show)

type Type = Expr

data Expr = Pi Name Type Type
          | Sigma Name Type Type
          | Lam Name Expr
          | Let Decl Expr
          | App Expr Expr
          | Meta
          | Var Name
          | Prim Name
  deriving (Show)
