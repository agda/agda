{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.TypeChecking.Positivity

module Agda.Interaction.JSON.TypeChecking.Positivity where

import Data.Aeson
import Agda.TypeChecking.Positivity.Occurrence

--------------------------------------------------------------------------------

instance ToJSON Occurrence where
  toJSON Mixed      = String "Mixed"
  toJSON JustNeg    = String "JustNeg"
  toJSON JustPos    = String "JustPos"
  toJSON StrictPos  = String "StrictPos"
  toJSON GuardPos   = String "GuardPos"
  toJSON Unused     = String "Unused"
