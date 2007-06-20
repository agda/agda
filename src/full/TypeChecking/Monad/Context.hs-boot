
module TypeChecking.Monad.Context where

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad.Base

getContext   :: MonadTCM tcm => tcm [Arg (Name, Type)]
getContextId :: MonadTCM tcm => tcm [CtxId]

