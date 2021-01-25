module Agda.Compiler.GoLang.Substitution where

import Prelude hiding ( map, lookup )
import Data.Map ( empty, unionWith, singleton, findWithDefault )
import qualified Data.Map as Map
import Data.List ( genericIndex )
import qualified Data.List as List

import Agda.Syntax.Common ( Nat )
import Agda.Compiler.GoLang.Syntax
  ( Exp(Undefined,Local,GoInterface),
    MemberId, LocalId(LocalId) )
import Agda.Utils.Function ( iterate' )
import Agda.Utils.List ( indexWithDefault )