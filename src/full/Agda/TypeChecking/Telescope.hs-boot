
module Agda.TypeChecking.Telescope where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

piApplyM :: Type -> Args -> TCM Type
