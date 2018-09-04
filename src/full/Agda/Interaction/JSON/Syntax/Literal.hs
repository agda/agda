{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Literal

module Agda.Interaction.JSON.Syntax.Literal where

import Data.Aeson

import Agda.Interaction.JSON.Syntax.Common
import Agda.Interaction.JSON.Syntax.Abstract
import Agda.Interaction.JSON.Syntax.Position
import Agda.Interaction.JSON.Utils

import Agda.Syntax.Literal

--------------------------------------------------------------------------------

instance ToJSON Literal where
  toJSON (LitNat range value) = object
    [ "kind"      .= String "LitNat"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitWord64 range value) = object
    [ "kind"      .= String "LitWord64"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitFloat range value) = object
    [ "kind"      .= String "LitFloat"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitString range value) = object
    [ "kind"      .= String "LitString"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitChar range value) = object
    [ "kind"      .= String "LitChar"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitQName range value) = object
    [ "kind"      .= String "LitQName"
    , "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitMeta range path metaId) = object
    [ "kind"      .= String "LitMeta"
    , "range"     .= range
    , "path"      .= path
    , "metaId"    .= metaId
    ]
