{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Primitive where

import Data.Map (Map)
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Builtin (PrimitiveId)
import Agda.Syntax.Internal (Type)

primitiveFunctions :: Map PrimitiveId (TCM (Maybe Type, PrimFun))
