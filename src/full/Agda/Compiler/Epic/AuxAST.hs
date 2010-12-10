{-# OPTIONS_GHC -Wall #-}
-- | Intermediate abstract syntax tree used in the compiler. Pretty close to
--   Epic syntax.
module Agda.Compiler.Epic.AuxAST where

import Data.Set (Set)
import qualified Data.Set as S

import Agda.Syntax.Abstract.Name

type Var = String
type Tag = Int

type Comment  = String
type Inline   = Bool

data Fun
  = Fun
      { funInline  :: Inline
      , funName    :: Var
      , funComment :: Comment
      , funArgs    :: [Var]
      , funExpr    :: Expr
      }
  | EpicFun
      { funName     :: Var
      , funComment  :: Comment
      , funEpicCode :: String --EpicCode
      }
  deriving (Eq, Ord, Show)

data Lit
  = LInt Integer
  | LChar Char
  | LString String
  deriving (Show, Ord, Eq)

data Expr
  = Var Var
  | Lit Lit
  | Lam Var Expr
  | Con Tag QName [Expr]
  | App Var [Expr]
  | Case Expr [Branch]
  | If Expr Expr Expr
  | Let Var Expr Expr
  | Lazy Expr
  | UNIT
  | IMPOSSIBLE
  deriving (Show, Ord, Eq)

data Branch
  = Branch  {brTag  :: Tag, brName :: QName, brVars :: [Var], brExpr :: Expr}
  | BrInt   {brInt  :: Int, brExpr :: Expr}
  | Default {brExpr :: Expr}
  deriving (Show, Ord, Eq)

-- | Smart constructor for applications to avoid empty applications
apps :: Var -> [Expr] -> Expr
apps v [] = Var v
apps v as = App v as

-- | Substitution
subst :: Var  -- ^ Substitute this ...
      -> Var  -- ^ with this ...
      -> Expr -- ^ in this.
      -> Expr
subst var var' expr = case expr of
    Var v      | var == v  -> Var var'
               | otherwise -> Var v
    Lit l -> Lit l
    Lam v e    | var == v  -> Lam v e
               | otherwise -> Lam v (subst var var' e)
    Con t q es -> Con t q (map (subst var var') es)
    App v es   | var == v  -> App var' (map (subst var var') es)
               | otherwise -> App v    (map (subst var var') es)
    Case e brs -> Case (subst var var' e) (map (substBranch var var') brs)
    If a b c -> let s = subst var var'
                 in If (s a) (s b) (s c)
    Let v e e' | var == v  -> Let v (subst var var' e) e'
               | otherwise -> Let v (subst var var' e) (subst var var' e')
    Lazy e     -> Lazy (subst var var' e)
    UNIT       -> UNIT
    IMPOSSIBLE -> IMPOSSIBLE

substBranch :: Var -> Var -> Branch -> Branch
substBranch x e br = br { brExpr = subst x e (brExpr br) }

-- | Get the free variables in an expression
fv :: Expr -> [Var]
fv = S.toList . fv'
  where
    fv' :: Expr -> Set Var
    fv' expr = case expr of
      Var v    -> S.singleton v
      Lit _    -> S.empty
      Lam v e1 -> S.delete v (fv' e1)
      Con _ _ es -> S.unions (map fv' es)
      App v es -> S.insert v $ S.unions (map fv' es)
      Case e brs -> fv' e `S.union` S.unions (map fvBr brs)
      If a b c   -> S.unions (map fv' [a,b,c])
      Let v e e' -> fv' e `S.union` (S.delete v $ fv' e')
      Lazy e     -> fv' e
      UNIT       -> S.empty
      IMPOSSIBLE -> S.empty

    fvBr :: Branch -> Set Var
    fvBr b = case b of
      Branch _ _ vs e -> fv' e S.\\ S.fromList vs
      BrInt _ e       -> fv' e
      Default e       -> fv' e

-- | Filter a list using a list of Bools specifying what to keep.
pairwiseFilter :: [Bool] -> [a] -> [a]
pairwiseFilter (True :bs) (a:as) = a : pairwiseFilter bs as
pairwiseFilter (False:bs) (_:as) = pairwiseFilter bs as
pairwiseFilter _           _     = []
