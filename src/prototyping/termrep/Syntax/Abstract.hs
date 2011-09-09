
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

-- Elim view --------------------------------------------------------------

data ElimView = NoElim Expr
              | ElimV Expr [Elim]

data Elim = Apply Expr
          | Fst
          | Snd

elimView :: Expr -> ElimView
elimView e = case e of
    App (Prim "fst") e -> elimView e `elim` Fst
    App (Prim "snd") e -> elimView e `elim` Snd
    App e1 e2 -> elimView e1 `elim` Apply e2
    _ -> NoElim e
  where
    elim (NoElim e)    el = ElimV e [el]
    elim (ElimV e els) el = ElimV e (els ++ [el])
