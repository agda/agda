{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.TypeChecking.Positivity

module Agda.Interaction.JSON.TypeChecking.Positivity where

import Data.Aeson
-- import Data.Function (on)
-- import Data.List (nub, sortBy)
-- import Data.Maybe (isJust)
-- import Data.Char (toLower)
-- import qualified Data.Set as Set
--
-- import Agda.Interaction.JSON.Encode
-- import Agda.Interaction.JSON.Syntax
-- import Agda.Interaction.JSON.Utils
--
-- import qualified Agda.Syntax.Abstract as A
-- import qualified Agda.Syntax.Common as C
-- import qualified Agda.Syntax.Concrete as C
-- import qualified Agda.Syntax.Concrete.Definitions as D
-- import qualified Agda.Syntax.Info as I
-- import qualified Agda.Syntax.Internal as I
-- import Agda.Syntax.Internal (dummySort)
-- import qualified Agda.Syntax.Position as P
-- import qualified Agda.Syntax.Scope.Monad as S
-- import qualified Agda.Syntax.Scope.Base as S
-- import qualified Agda.Syntax.Translation.AbstractToConcrete as Trans
-- import Agda.Syntax.Translation.InternalToAbstract (Reify(..))
--
-- import Agda.Syntax.Position (Range, Range'(..))
--
-- import Agda.TypeChecking.Errors
-- import Agda.TypeChecking.Monad
-- import Agda.TypeChecking.Monad.Context (inTopContext)
-- import Agda.TypeChecking.Substitute (Abstract(..), raise)
-- import Agda.TypeChecking.Monad.Builtin
-- import Agda.TypeChecking.Pretty (PrettyTCM(..), prettyA, prettyPattern)
-- import Agda.TypeChecking.Telescope (ifPiType)
import Agda.TypeChecking.Positivity.Occurrence

-- import Agda.Utils.Pretty (render, pretty, prettyShow)
-- import Agda.Utils.FileName (filePath)
-- import Agda.Utils.Size (size)
-- import Agda.Utils.List
-- import Agda.Utils.NonemptyList (NonemptyList(..), toList)

--------------------------------------------------------------------------------
-- Agda.TypeChecking.Positivity.Occurrence

instance ToJSON Occurrence where
  toJSON Mixed      = String "Mixed"
  toJSON JustNeg    = String "JustNeg"
  toJSON JustPos    = String "JustPos"
  toJSON StrictPos  = String "StrictPos"
  toJSON GuardPos   = String "GuardPos"
  toJSON Unused     = String "Unused"
