module Agda.Syntax.Internal where

import Control.DeepSeq

import {-# SOURCE #-} Agda.Syntax.Position (KillRange)

data Term

instance Show Term
instance NFData Term
instance KillRange Term
