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
import Agda.Syntax.Literal

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
  = CoreFun
      { xfunName     :: HsName
      , xfunQName    :: Maybe QName
      , xfunComment  :: Comment
      , xfunCoreExpr :: CExpr
      }
  deriving (Eq, Show)


-- | Returns the arity of a constructor.
xconArity :: ADataCon -> Int
xconArity = getCTagArity . xconCTag

getCTagArity :: CTag -> Int
-- for records/datatypes, we can always extract the arity. If there is no arity,
-- it is the unit constructor, so just return zero.
getCTagArity = destructCTag 0 (\_ _ _ ar -> ar)

