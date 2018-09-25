{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Concrete.Name

module Agda.Interaction.JSON.Syntax.Concrete.Name where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Common
import Agda.Interaction.JSON.Syntax.Position
import Agda.Syntax.Concrete.Name

--------------------------------------------------------------------------------

instance ToJSON NamePart where
  toJSON Hole      = Null
  toJSON (Id name) = toJSON name

instance EncodeTCM Name where
instance ToJSON Name where
  toJSON (Name   range parts) = kind' "Name"
    [ "range" .= range
    , "parts" .= parts
    ]
  toJSON (NoName range name) = kind' "NoName"
    [ "range" .= range
    , "name"  .= name
    ]

instance EncodeTCM QName where
instance ToJSON QName where
  toJSON = toJSON . toList
    where
      toList (QName name)      = name : []
      toList (Qual name qname) = name : toList qname

instance EncodeTCM TopLevelModuleName
instance ToJSON TopLevelModuleName where
  toJSON (TopLevelModuleName range parts) = object
    [ "range" .= range
    , "parts" .= parts
    ]
