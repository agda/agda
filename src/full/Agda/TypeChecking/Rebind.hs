{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rebind where

import Agda.Syntax.Internal
import Agda.TypeChecking.Free
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Change 'Bind's to 'NoBind' if the variable is not used in the body.
--   Also normalises the body in the process. Or not. Disabled.
rebindClause :: Clause -> TCM Clause
rebindClause (Clause tel perm ps b) = return $ Clause tel perm ps b
{-
  do
    b <- instantiateFull b
    return $ Clause ps $ rebind b
    where
	rebind (Body t) = Body t
	rebind (Bind b)
	    | 0 `freeIn` absBody b  = Bind $ fmap rebind b
	    | otherwise		    = NoBind $ b `absApp` __IMPOSSIBLE__
	rebind (NoBind b) = NoBind $ rebind b
	rebind  NoBody	  = NoBody
-}

