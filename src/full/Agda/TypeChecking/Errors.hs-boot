module Agda.TypeChecking.Errors where

import Agda.TypeChecking.Monad.Base

prettyError :: TCErr -> TCM String
