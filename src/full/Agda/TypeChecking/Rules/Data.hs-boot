{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rules.Data where

import Agda.Syntax.Internal         ( QName, Sort )
import Agda.TypeChecking.Monad.Base ( TCM )

checkDataSort :: QName -> Sort -> TCM ()
