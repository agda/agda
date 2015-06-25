{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
-- | Intermediate abstract syntax tree used in the compiler. Pretty close to
--   UHC Core syntax.
module Agda.Compiler.UHC.AuxAST
  ( module Agda.Compiler.UHC.AuxAST
  , CTag
  , HsName
  , CExpr
  )
where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)

import Agda.Syntax.Abstract.Name

import Agda.Compiler.UHC.Bridge (HsName, CTag, CExpr, destructCTag)

#include "undefined.h"
import Agda.Utils.Impossible

type Tag = Int
type Comment  = String
type Inline   = Bool
type CType = Maybe HsName -- Nothing for Unit, else the name

data AMod
  = AMod
      { xmodName    :: ModuleName
      , xmodDataTys :: [ADataTy]
      , xmodFunDefs :: [Fun]
      , xmodCrImports :: Set String -- ^ Imports of other Core/Haskell modules for the FFI. Includes transitive imports.
      }

data ADataTy
  = ADataTy
      { xdatName     :: CType
      , xdatQName    :: QName
      , xdatCons     :: [ADataCon]
      , xdatImplType :: ADataImplType
      }
  deriving (Eq, Ord, Show, Typeable)

data ADataImplType
  = ADataImplNormal  -- normal agda datatype
  | ADataImplMagic String -- COMPILED_DATA_UHC mapping to one of the
                          -- magic builtin types, eg __UNIT__.
  | ADataImplForeign -- COMPILED_DATA_UHC pragma mapping to a normal UHC Core datatype
                     -- defined by non-Agda code (e.g. Haskell).
  deriving (Eq, Ord, Show, Typeable)

data ADataCon
  = ADataCon
      { xconQName    :: QName
      , xconCTag     :: CTag
      }
  deriving (Eq, Ord, Show, Typeable)

data Fun
  = Fun
      { xfunInline  :: Inline
      , xfunName    :: HsName
      , xfunQName   :: Maybe QName
      , xfunComment :: Comment
      , xfunArgs    :: [HsName] -- args will always be empty right now, we use lambdas inside the body instead.
                                -- Would be nicer to have them here, but coinduction (copatterns) make this tricky.
      , xfunExpr    :: Expr
      }
  | CoreFun
      { xfunName     :: HsName
      , xfunQName    :: Maybe QName
      , xfunComment  :: Comment
      , xfunCoreExpr :: CExpr
      }
  deriving (Eq, Show)

data Lit
  = LInt    Integer
  | LChar   Char
  | LString String
  | LFloat  Double
  | LQName  QName
  deriving (Show, Ord, Eq)


data CaseType
  = CTCon ADataTy -- rename this to CTData
  | CTChar
  | CTString
  deriving (Show, Ord, Eq)

data Expr
  = Var HsName
  | Lit Lit
  | Lam HsName Expr
  | Con ADataTy ADataCon [Expr]
  | App Expr [Expr]
  | Case Expr [Branch] Expr CaseType -- scrutinee, alts, default, case ty
  | Let HsName Expr Expr
  | UNIT    -- ^ Used for internally generated unit values. If an Agda datatype is bound to the
            -- Unit builtin, two representations of unit exists, but will be compiled to the same
            -- thing.
  | IMPOSSIBLE
  deriving (Show, Ord, Eq)

data Branch
  = BrCon   {brCon  :: ADataCon, brName :: QName, brVars :: [HsName], brExpr :: Expr}
  | BrChar  {brChar :: Char, brExpr :: Expr}
  | BrString {brStr :: String, brExpr :: Expr}
  deriving (Show, Ord, Eq)

-- | Returns the arity of a constructor.
xconArity :: ADataCon -> Int
xconArity = getCTagArity . xconCTag

getCTagArity :: CTag -> Int
-- for records/datatypes, we can always extract the arity. If there is no arity,
-- it is the unit constructor, so just return zero.
getCTagArity = destructCTag 0 (\_ _ _ ar -> ar)

getBrVars :: Branch -> [HsName]
getBrVars (BrCon {brVars = vs}) = vs
getBrVars (BrChar {})            = []
getBrVars (BrString {})          = []

--------------------------------------------------------------------------------
-- * Some smart constructors

-- | Smart constructor for let expressions to avoid unneceessary lets
lett :: HsName -> Expr -> Expr -> Expr
lett v (Var v') e' = subst v v' e'
lett v e        e' = if v `elem` fv e' then Let v e e' else e'

--   TODO we should use the type information from inside the case statement to also handle defaults and literals.
-- | If casing on the same expression in a sub-expression, we know what branch to
--   pick
casee :: ADataTy -> Expr -> [Branch] -> Expr -> CaseType -> Expr
casee _ x brs def cty = Case x [br{brExpr = casingE br (brExpr br)} | br <- brs] def cty
  where
    casingE br expr = let rec = casingE br in case expr of
      Var v -> Var v
      Lit l -> Lit l
      Lam v e -> Lam v (rec e)
      Con t n es -> Con t n (map rec es)
      App v es   -> App v (map rec es)
      Case e brs' def' cty' | expr == e -> case filter (sameCon br) brs' of
        []  -> Case (rec e) [b {brExpr = rec (brExpr b)} | b <- brs'] (rec def') cty'
        [b] -> substs (getBrVars br `zip` getBrVars b) (brExpr b)
        _   -> __IMPOSSIBLE__
                 | otherwise -> Case (rec e) [b {brExpr = rec (brExpr b)} | b <- brs'] (rec def') cty'
      Let v e1 e2 -> Let v (rec e1) (rec e2)
      UNIT        -> UNIT
      IMPOSSIBLE  -> IMPOSSIBLE
    sameCon (BrCon {brCon = c1}) (BrCon {brCon = c2}) = c1 == c2
    sameCon _                     _                     = False

-- | Smart constructor for applications to avoid empty applications
apps :: Expr -> [Expr] -> Expr
apps v [] = v
apps v as = App v as

apps1 :: HsName -> [Expr] -> Expr
apps1 v = apps (Var v)

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
    App v es   -> App (subst var var' v) (map (subst var var') es)
    Case e brs def ty -> Case (subst var var' e) (map (substBranch var var') brs) (subst var var' def) ty
    Let v e e' | var == v  -> Let v (subst var var' e) e'
               | otherwise -> Let v (subst var var' e) (subst var var' e')
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
      App v es -> S.unions (fv' v : map fv' es)
      Case e brs def _ -> fv' e `S.union` S.unions (map fvBr brs) `S.union` (fv' def)
      Let v e e' -> fv' e `S.union` (S.delete v $ fv' e')
      UNIT       -> S.empty
      IMPOSSIBLE -> S.empty

    fvBr :: Branch -> Set HsName
    fvBr b = case b of
      BrCon _ _ vs e -> fv' e S.\\ S.fromList vs
      BrChar _ e -> fv' e
      BrString _ e -> fv' e
