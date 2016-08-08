
module Agda.TypeChecking.Telescope where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute

piApplyM :: Type -> Args -> TCM Type
telView :: Type -> TCM TelView
