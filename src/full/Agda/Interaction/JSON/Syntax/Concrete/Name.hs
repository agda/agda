{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Concrete.Name

module Agda.Interaction.JSON.Syntax.Concrete.Name where

import Data.Aeson

import Agda.Interaction.JSON.Syntax.Common
import Agda.Interaction.JSON.Syntax.Position
import Agda.Interaction.JSON.Utils
import Agda.Syntax.Concrete.Name

--------------------------------------------------------------------------------

instance ToJSON Name where
  toJSON (Name   range parts) = object
    [ "kind"  .= String "Name"
    , "range" .= range
    , "parts" .= parts
    ]
  toJSON (NoName range name) = object
    [ "kind"  .= String "NoName"
    , "range" .= range
    , "name"  .= name
    ]

instance ToJSON NamePart where
  toJSON Hole      = Null
  toJSON (Id name) = toJSON name

instance ToJSON QName where
  toJSON = toJSON . toList
    where
      toList (QName name)      = name : []
      toList (Qual name qname) = name : toList qname
