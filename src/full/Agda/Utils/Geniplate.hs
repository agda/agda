{-# LANGUAGE TemplateHaskell #-}

-- | Utilities related to Geniplate.

module Agda.Utils.Geniplate
  ( instanceUniverseBiT'
  , instanceTransformBiMT'
  , dontDescendInto
  ) where

import Data.Generics.Geniplate
import Data.Map (Map)

import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Scope.Base as S

-- | Types which Geniplate should not descend into.

dontDescendInto =
  [ [t| String |]
  , [t| A.QName |]
  , [t| A.Name |]
  , [t| C.Name |]
  , [t| S.ScopeInfo |]
  , [t| Map A.QName A.QName |]
  , [t| Map A.ModuleName A.ModuleName |]
  , [t| A.AmbiguousQName |]
  ]

-- | A localised instance of 'instanceUniverseBiT'. The generated
-- 'universeBi' functions neither descend into the types in
-- 'dontDescendInto', nor into the types in the list argument.

instanceUniverseBiT' ts p =
  instanceUniverseBiT (ts ++ dontDescendInto) p

-- | A localised instance of 'instanceTransformBiMT'. The generated
-- 'transformBiM' functions neither descend into the types in
-- 'dontDescendInto', nor into the types in the list argument.

instanceTransformBiMT' ts p =
  instanceTransformBiMT (ts ++ dontDescendInto) p
