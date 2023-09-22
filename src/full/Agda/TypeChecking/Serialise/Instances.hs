{-# OPTIONS_GHC -Wunused-imports #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Only instances exported
module Agda.TypeChecking.Serialise.Instances () where

import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common (SerialisedRange(..))
import Agda.TypeChecking.Serialise.Instances.Highlighting ()
import Agda.TypeChecking.Serialise.Instances.Errors ()
import Agda.Utils.Hash

type RangedImportedModules =
  [(SerialisedRange, TopLevelModuleName, Hash)]

fromImportedModules ::
  [(TopLevelModuleName, Hash)] -> RangedImportedModules
fromImportedModules ms = [(SerialisedRange $ getRange x, x, hash) | (x, hash) <- ms]

toImportedModules ::
  RangedImportedModules -> [(TopLevelModuleName, Hash)]
toImportedModules ms = [(setRange (underlyingRange r) x, hash) | (r, x, hash) <- ms]

instance EmbPrj Interface where
  icod_ (Interface a b c d e f g h i j k l m n o p q r s t u v w x) =
      icodeN' interface a b c (fromImportedModules d) e f g h i j k l m n o p q r s t u v w x
    where interface a b c = Interface a b c . toImportedModules

  value = valueN interface
    where interface a b c = Interface a b c . toImportedModules
