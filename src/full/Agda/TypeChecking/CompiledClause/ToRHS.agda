-- | Trailing inductive copattern matches on the LHS can be savely
--   translated to record expressions on RHS, without jeopardizing
--   termination.
--
{-# LANGUAGE CPP #-}
module Agda.TypeChecking.CompiledClause.ToRHS where

-- import Control.Applicative
import Data.Monoid
import qualified Data.Map as Map
import Data.List (genericReplicate, nubBy, findIndex)
import Data.Function

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty

import Agda.Utils.List
import Agda.Utils.Impossible
#include "../../undefined.h"
