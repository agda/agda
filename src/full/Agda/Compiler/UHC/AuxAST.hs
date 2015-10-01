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

