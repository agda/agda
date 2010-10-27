
module Internal where

import Text.PrettyPrint
import Data.Map (Map)
import qualified Data.Map as Map

import Abstract (Var, Name)
import qualified Abstract as A
import qualified Scope as A
import Pretty
import Utils

data Type = Pi Type (Abs Type)
	  | Set
	  | El Term

data Term = Lam (Abs Term)
	  | App Term Term
	  | Def Name
	  | Var Int

data Abs a = Abs { absName :: Var, unAbs :: a }

data Defn = Type  { defName :: Name, defFreeVars :: Int, defType :: Type }
	  | Value { defName :: Name, defFreeVars :: Int, defType :: Type, _defValue :: Term }

-- To abstract ------------------------------------------------------------

instance Pretty Term where prettyPrec n = prettyPrec n . toExpr []
instance Pretty Type where prettyPrec n = prettyPrec n . toExpr []

class ToExpr a where
    toExpr :: [Var] -> a -> A.Expr

instance ToExpr Type where
    toExpr ctx a = case a of
	Set    -> A.Set
	Pi a b -> A.Pi (fresh ctx $ absName b) (toExpr ctx a) (toExpr ctx b)
	El t   -> toExpr ctx t

instance ToExpr Term where
    toExpr ctx t = case t of
	Lam t	-> A.Lam (fresh ctx $ absName t) $ toExpr ctx t
	App s t -> (A.App `on` toExpr ctx) s t
	Var n	-> A.Var $ ctx !!! n
	Def c	-> A.Def c

instance ToExpr a => ToExpr (Abs a) where
    toExpr ctx (Abs x b) = toExpr (fresh ctx x : ctx) b

xs !!! n
    | length xs <= n = "BAD" ++ show (n - length xs)
    | otherwise	     = xs !! n

fresh :: [Var] -> Var -> Var
fresh _ "_" = "_"
fresh ctx x
    | elem x ctx = head [ x' | x' <- variants x, notElem x' ctx ]
    | otherwise   = x

variants :: Var -> [Var]
variants x = map (x ++) $ "'" : [ show n | n <- [0..] ]
