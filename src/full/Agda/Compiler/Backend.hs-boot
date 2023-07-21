{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Backend
  ( module Agda.Syntax.Treeless
  , Backend
  , activeBackendMayEraseType
  , lookupBackend
  )
  where

import Control.DeepSeq

-- Explicitly adding the Agda.Syntax.Treeless import to the .hs-boot file
-- so that the `Args` symbol can be hidden by the `SOURCE` import in
-- TypeChecking.Monad.Base.
--
-- Without exporting it here, a `hiding` clause there causes a compilation
-- error. But without hiding it there, the name conflicts with the one
-- imported from Agda.Syntax.Internal.
--
-- This is only a problem with ghci, which will load a fully-compiled module if
-- available; but that module will contain more symbols than just the few in
-- the .hs-boot
import Agda.Syntax.Treeless (TTerm, Args)

import Agda.Syntax.Abstract.Name (QName)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base (TCM, BackendName)

data Backend

instance NFData Backend

activeBackendMayEraseType :: QName -> TCM Bool
lookupBackend :: BackendName -> TCM (Maybe Backend)
