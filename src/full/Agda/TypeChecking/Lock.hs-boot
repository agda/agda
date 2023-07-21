{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.Lock where

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
-- import Agda.TypeChecking.Monad.Context
-- import Agda.TypeChecking.Pretty
-- import Agda.TypeChecking.Reduce
-- import Agda.TypeChecking.Substitute.Class
-- import Agda.TypeChecking.Telescope
-- import Agda.TypeChecking.Free

-- import Agda.Utils.Function
-- import Agda.Utils.Lens
-- import Agda.Utils.Maybe
-- import Agda.Utils.Monad
-- import Agda.Utils.Size

-- #include "undefined.h"
-- import Agda.Utils.Impossible



checkLockedVars
  :: Term
     -- ^ term to check
  -> Type
     -- ^ its type
  -> Arg Term
     -- ^ the lock
  -> Type
     -- ^ type of the lock
  -> TCM ()
