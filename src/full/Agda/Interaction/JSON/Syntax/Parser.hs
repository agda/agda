{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Parser

module Agda.Interaction.JSON.Syntax.Parser where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Position
import Agda.Syntax.Parser


--------------------------------------------------------------------------------

instance EncodeTCM ParseWarning where
instance ToJSON ParseWarning where
  toJSON (OverlappingTokensWarning range) = object
    [ "range"  .= range
    ]
