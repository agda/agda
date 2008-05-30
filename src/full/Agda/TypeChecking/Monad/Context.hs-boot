
module Agda.TypeChecking.Monad.Context where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

getContext   :: MonadTCM tcm => tcm [Arg (Name, Type)]
getContextId :: MonadTCM tcm => tcm [CtxId]

