{-# LANGUAGE CPP #-}
-- | Intermediate abstract syntax tree used in the compiler. Pretty close to
--   Epic syntax.
module Agda.Compiler.UHC.AuxAST where

import Data.Set (Set)
import qualified Data.Set as S

import Agda.Syntax.Abstract.Name

import Agda.Compiler.UHC.CoreSyntax (CoreExpr, CoreConstr)
import Agda.Compiler.UHC.Interface

#include "../../undefined.h"
import Agda.Utils.Impossible

type Comment  = String
type Inline   = Bool

data Fun
  = Fun
      { funInline  :: Inline
      , funName    :: AName
      , funQName   :: Maybe QName
      , funComment :: Comment
      , funArgs    :: [AName]
      , funExpr    :: Expr
      }
  | CoreFun
      { funName     :: AName
      , funQName    :: Maybe QName
      , funComment  :: Comment
      , funCoreExpr :: CoreExpr
      }
  deriving (Eq, Show)

data Lit
  = LInt    Integer
  | LChar   Char
  | LString String
  | LFloat  Double
  deriving (Show, Ord, Eq)



data Expr
  = Var AName
  | Lit Lit
  | Lam AName Expr
  | Con Tag QName [Expr]
  | App AName [Expr]
  | Case Expr [Branch]
  | Let AName Expr Expr
  | UNIT
  | IMPOSSIBLE
  deriving (Show, Ord, Eq)

data Branch
  = Branch  {brTag  :: Tag, brName :: QName, brVars :: [AName], brExpr :: Expr}
  | CoreBranch {brCoreCon :: CoreConstr, brVars :: [AName], brExpr :: Expr}
  | BrInt   {brInt  :: Int, brExpr :: Expr}
  | Default {brExpr :: Expr}
  deriving (Show, Ord, Eq)

getBrVars :: Branch -> [AName]
getBrVars (Branch {brVars = vs}) = vs
getBrVars (CoreBranch {brVars = vs}) = vs
getBrVars _                      = []

--------------------------------------------------------------------------------
-- * Some smart constructors

-- | Smart constructor for let expressions to avoid unneceessary lets
lett :: AName -> Expr -> Expr -> Expr
lett v (Var v') e' = subst v v' e'
lett v e        e' = if v `elem` fv e' then Let v e e' else e'

-- | If casing on the same expression in a sub-expression, we know what branch to
--   pick
casee :: Expr -> [Branch] -> Expr
casee x brs = Case x [br{brExpr = casingE br (brExpr br)} | br <- brs]
  where
    casingE br expr = let rec = casingE br in case expr of
      Var v -> Var v
      Lit l -> Lit l
      Lam v e -> Lam v (rec e)
      Con t n es -> Con t n (map rec es)
      App v es   -> App v (map rec es)
      Case e brs | expr == e -> case filter (sameCon br) brs of
        []  -> Case (rec e) [b {brExpr = rec (brExpr b)} | b <- brs]
        [b] -> substs (getBrVars br `zip` getBrVars b) (brExpr b)
        _   -> __IMPOSSIBLE__
                 | otherwise -> Case (rec e) [b {brExpr = rec (brExpr b)} | b <- brs]
--      If e1 e2 e3 -> If (rec e1) (rec e2) (rec e3)
      Let v e1 e2 -> Let v (rec e1) (rec e2)
--      Lazy e      -> Lazy (rec e)
      UNIT        -> UNIT
      IMPOSSIBLE  -> IMPOSSIBLE
    sameCon (Branch {brTag = t1}) (Branch {brTag = t2}) = t1 == t2
    sameCon (BrInt  {brInt = i1}) (BrInt  {brInt = i2}) = i1 == i2
    sameCon _                     _                     = False

-- | Smart constructor for applications to avoid empty applications
apps :: AName -> [Expr] -> Expr
apps v [] = Var v
apps v as = App v as

--------------------------------------------------------------------------------
-- * Substitution

-- | Substitution
subst :: AName  -- ^ Substitute this ...
      -> AName  -- ^ with this ...
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
--    If a b c -> let s = subst var var'
--                 in If (s a) (s b) (s c)
    Let v e e' | var == v  -> Let v (subst var var' e) e'
               | otherwise -> Let v (subst var var' e) (subst var var' e')
--    Lazy e     -> Lazy (subst var var' e)
    UNIT       -> UNIT
    IMPOSSIBLE -> IMPOSSIBLE

substs :: [(AName, AName)] -> Expr -> Expr
substs ss e = foldr (uncurry subst) e ss

substBranch :: AName -> AName -> Branch -> Branch
substBranch x e br = br { brExpr = subst x e (brExpr br) }

-- | Get the free variables in an expression
fv :: Expr -> [AName]
fv = S.toList . fv'
  where
    fv' :: Expr -> Set AName
    fv' expr = case expr of
      Var v    -> S.singleton v
      Lit _    -> S.empty
      Lam v e1 -> S.delete v (fv' e1)
      Con _ _ es -> S.unions (map fv' es)
      App v es -> S.insert v $ S.unions (map fv' es)
      Case e brs -> fv' e `S.union` S.unions (map fvBr brs)
--      If a b c   -> S.unions (map fv' [a,b,c])
      Let v e e' -> fv' e `S.union` (S.delete v $ fv' e')
--      Lazy e     -> fv' e
      UNIT       -> S.empty
      IMPOSSIBLE -> S.empty

    fvBr :: Branch -> Set AName
    fvBr b = case b of
      Branch _ _ vs e -> fv' e S.\\ S.fromList vs
      CoreBranch _ vs e -> fv' e S.\\ S.fromList vs
      BrInt _ e       -> fv' e
      Default e       -> fv' e
