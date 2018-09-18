{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Parser

module Agda.Interaction.JSON.Syntax.Parser where

import Data.Aeson

import Agda.Interaction.JSON.Syntax.Position
import Agda.Interaction.JSON.Utils
import Agda.Syntax.Parser


--------------------------------------------------------------------------------

instance ToJSON ParseWarning where
  toJSON (OverlappingTokensWarning range) = object
    [ "range"  .= range
    ]
