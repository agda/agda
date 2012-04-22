------------------------------------------------------------------------
-- Pretty-printing of Haskell modules
------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, TemplateHaskell #-}

module Agda.Compiler.MAlonzo.Pretty where

import Data.Generics.Geniplate
import qualified Language.Haskell.Exts.Pretty as Pretty
import qualified Language.Haskell.Exts.Syntax as HS

import Agda.Compiler.MAlonzo.Encode

-- | Encodes module names just before pretty-printing.

prettyPrint :: (Pretty.Pretty a, TransformBi HS.ModuleName (Wrap a)) =>
               a -> String
prettyPrint = Pretty.prettyPrint .
              unwrap .
              transformBi encodeModuleName .
              Wrap

-- | A wrapper type used to avoid orphan instances.

newtype Wrap a = Wrap { unwrap :: a }

-- Some TransformBiT instances.

instanceTransformBiT [ [t| String |] ] [t| (HS.ModuleName, Wrap HS.Exp)        |]
instanceTransformBiT [ [t| String |] ] [t| (HS.ModuleName, Wrap HS.Module)     |]
instanceTransformBiT [ [t| String |] ] [t| (HS.ModuleName, Wrap HS.ModuleName) |]
instanceTransformBiT [ [t| String |] ] [t| (HS.ModuleName, Wrap HS.QName)      |]
