
module Implementation.Simple.Eval where

import Types.Blocked
import Implementation.Simple.Term
import Implementation.Simple.Monad

whnf :: MonadEval m => Term -> m (Blocked Term)
whnf v = return $ NotBlocked v

