{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Literal

module Agda.Interaction.JSON.Syntax.Literal where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Common
import Agda.Interaction.JSON.Syntax.Position

import Agda.Syntax.Literal
import Agda.Utils.Pretty (prettyShow)

--------------------------------------------------------------------------------

instance ToJSON Literal where
  toJSON (LitNat range value) = kind' "LitNat"
    [ "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitWord64 range value) = kind' "LitWord64"
    [ "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitFloat range value) = kind' "LitFloat"
    [ "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitString range value) = kind' "LitString"
    [ "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitChar range value) = kind' "LitChar"
    [ "range"     .= range
    , "value"     .= value
    ]
  toJSON (LitQName range value) = kind' "LitQName"
    [ "range"     .= range
    , "value"     .= prettyShow value
    ]
  toJSON (LitMeta range path metaId) = kind' "LitMeta"
    [ "range"     .= range
    , "path"      .= path
    , "metaId"    .= metaId
    ]
