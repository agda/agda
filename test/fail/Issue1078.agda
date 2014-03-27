-- {-# OPTIONS -v import:10 -v scope:10 #-}

module Issue1078 where

import Common.Level
import Issue1078.A
import Issue1078.B

-- Was: weird scope error in Issue1078.B

-- Should give error:
-- You tried to load Issue1078/B.agda
-- which defines the module Issue1078.A. However, according to the
-- include path this module should be defined in Issue1078/A.agda.
