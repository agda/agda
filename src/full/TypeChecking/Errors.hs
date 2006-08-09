
module TypeChecking.Errors where

import Syntax.Internal
import Syntax.Translation.InternalToAbstract
import Syntax.Translation.AbstractToConcrete
import TypeChecking.Monad

prettyError :: TCErr -> TCM String
prettyError = return . show

