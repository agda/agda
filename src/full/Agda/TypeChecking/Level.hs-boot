
module Agda.TypeChecking.Level where

import Agda.TypeChecking.Monad
import Agda.Syntax.Internal

levelView :: Term -> TCM Level
