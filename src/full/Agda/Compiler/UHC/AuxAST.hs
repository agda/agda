{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
-- | Intermediate abstract syntax tree used in the compiler. Pretty close to
--   UHC Core syntax.
module Agda.Compiler.UHC.AuxAST
  ( module Agda.Compiler.UHC.AuxAST
  , CTag
  , HsName
  )
where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)

import Agda.Syntax.Abstract.Name

import UHC.Light.Compiler.Core.API (HsName, CTag)
import Agda.Compiler.UHC.CoreSyntax (CoreExpr)

#include "undefined.h"
import Agda.Utils.Impossible

type Tag = Int
type Comment  = String
type Inline   = Bool

data AMod
  = AMod
      { xmodName    :: ModuleName
      , xmodDataTys :: [ADataTy]
      , xmodFunDefs :: [Fun]
      }

data ADataTy
  = ADataTy
      { xdatName     :: Maybe HsName -- ^ Datatype core name. Nothing for unit datatype.
      , xdatQName    :: QName
      , xdatCons     :: [ADataCon]
      , xdatImplType :: ADataImplType
      }
  deriving (Eq, Ord, Show, Typeable)

data ADataImplType
  = ADataImplNormal  -- normal agda datatype
  | ADataImplBuiltin String
  | ADataImplForeign -- COMPILED_CORE pragma
  deriving (Eq, Ord, Show, Typeable)

data ADataCon
  = ADataCon
      { xconQName    :: QName
      , xconArity    :: Int
      , xconCTag     :: CTag
      }
  deriving (Eq, Ord, Show, Typeable)

data Fun
  = Fun
      { xfunInline  :: Inline
      , xfunName    :: HsName
      , xfunQName   :: Maybe QName
      , xfunComment :: Comment
      , xfunArgs    :: [HsName]
      , xfunExpr    :: Expr
      }
  | CoreFun
      { xfunName     :: HsName
      , xfunQName    :: Maybe QName
      , xfunComment  :: Comment
      , xfunCoreExpr :: CoreExpr
      , xfunArity    :: Int -- TODO check if still used, remove if not
      }
  deriving (Eq, Show)

data Lit
  = LInt    Integer
  | LChar   Char
  | LString String
  | LFloat  Double
  deriving (Show, Ord, Eq)



data Expr
  = Var HsName
  | Lit Lit
  | Lam HsName Expr
  | Con ADataTy ADataCon [Expr]
  | App HsName [Expr]
  | Case Expr [Branch]
  | Let HsName Expr Expr
  | UNIT    -- ^ Used for internally generated unit values. If an Agda datatype is bound to the
            -- Unit builtin, two representations of unit exists, but will be compiled to the same
            -- thing.
  | IMPOSSIBLE
  deriving (Show, Ord, Eq)

-- TODO we should move brDataTy to Case (branches have to be on the same datatype)
data Branch
  = Branch  {brCon  :: ADataCon, brName :: QName, brVars :: [HsName], brExpr :: Expr}
--  | CoreBranch {brCoreCon :: CoreConstr, brVars :: [HsName], brExpr :: Expr}
  | Default {brExpr :: Expr}
  deriving (Show, Ord, Eq)

-- TODO check if still used, remove if not
funArity :: Fun -> Int
funArity (Fun {xfunArgs = args}) = length args
funArity (CoreFun {xfunArity = ar}) = ar

getBrVars :: Branch -> [HsName]
getBrVars (Branch {brVars = vs}) = vs
--getBrVars (CoreBranch {brVars = vs}) = vs
getBrVars _                      = []

--------------------------------------------------------------------------------
-- * Some smart constructors

-- | Smart constructor for let expressions to avoid unneceessary lets
lett :: HsName -> Expr -> Expr -> Expr
lett v (Var v') e' = subst v v' e'
lett v e        e' = if v `elem` fv e' then Let v e e' else e'

-- | If casing on the same expression in a sub-expression, we know what branch to
--   pick
casee :: ADataTy -> Expr -> [Branch] -> Expr
casee ty x brs = Case x [br{brExpr = casingE br (brExpr br)} | br <- brs]
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
    sameCon (Branch {brCon = c1}) (Branch {brCon = c2}) = c1 == c2
    sameCon _                     _                     = False

-- | Smart constructor for applications to avoid empty applications
apps :: HsName -> [Expr] -> Expr
apps v [] = Var v
apps v as = App v as

--------------------------------------------------------------------------------
-- * Substitution

-- | Substitution
subst :: HsName  -- ^ Substitute this ...
      -> HsName  -- ^ with this ...
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

substs :: [(HsName, HsName)] -> Expr -> Expr
substs ss e = foldr (uncurry subst) e ss

substBranch :: HsName -> HsName -> Branch -> Branch
substBranch x e br = br { brExpr = subst x e (brExpr br) }

-- | Get the free variables in an expression
fv :: Expr -> [HsName]
fv = S.toList . fv'
  where
    fv' :: Expr -> Set HsName
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

    fvBr :: Branch -> Set HsName
    fvBr b = case b of
      Branch _ _ vs e -> fv' e S.\\ S.fromList vs
--      CoreBranch _ vs e -> fv' e S.\\ S.fromList vs
      Default e       -> fv' e
