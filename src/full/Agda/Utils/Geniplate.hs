{-# LANGUAGE TemplateHaskell #-}

-- | Utilities related to Geniplate.

module Agda.Utils.Geniplate
  ( instanceUniverseBiT'
  , instanceTransformBiMT'
  , dontDescendInto
  ) where

import Data.Generics.Geniplate
import Data.Map (Map)

import qualified Language.Haskell.TH as TH

import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Position as P
import qualified Agda.Syntax.Scope.Base as S
import qualified Agda.Utils.FileName as F
import qualified Agda.Utils.Maybe.Strict as MS

-- | Types which Geniplate should not descend into.

dontDescendInto :: [TH.TypeQ]
dontDescendInto =
  [ [t| String |]
  , [t| A.QName |]
  , [t| A.Name |]
  , [t| C.Name |]
  , [t| S.ScopeInfo |]
  , [t| Map A.QName A.QName |]
  , [t| Map A.ModuleName A.ModuleName |]
  , [t| [(A.QName, A.QName)] |]
  , [t| [(A.ModuleName, A.ModuleName)] |]
  , [t| A.AmbiguousQName |]
  , [t| P.Range' (MS.Maybe F.AbsolutePath) |]
  ]

-- | A localised instance of 'instanceUniverseBiT'. The generated
-- 'universeBi' functions neither descend into the types in
-- 'dontDescendInto', nor into the types in the list argument.

instanceUniverseBiT' :: [TH.TypeQ] -> TH.TypeQ -> TH.Q [TH.Dec]
instanceUniverseBiT' ts p =
  instanceUniverseBiT (ts ++ dontDescendInto) p

-- | A localised instance of 'instanceTransformBiMT'. The generated
-- 'transformBiM' functions neither descend into the types in
-- 'dontDescendInto', nor into the types in the list argument.

instanceTransformBiMT' :: [TH.TypeQ] -> TH.TypeQ -> TH.TypeQ -> TH.Q [TH.Dec]
instanceTransformBiMT' ts p =
  instanceTransformBiMT (ts ++ dontDescendInto) p
