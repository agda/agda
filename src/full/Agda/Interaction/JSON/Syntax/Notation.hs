{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Notation

module Agda.Interaction.JSON.Syntax.Notation where

import Data.Aeson

import Agda.Interaction.JSON.Syntax.Common
import Agda.Syntax.Notation


--------------------------------------------------------------------------------

instance ToJSON GenPart where
  toJSON (BindHole n) = object
    [ "kind"      .= String "BindHole"
    , "position"  .= n
    ]
  toJSON (NormalHole n) = object
    [ "kind"      .= String "NormalHole"
    , "position"  .= n
    ]
  toJSON (WildHole n) = object
    [ "kind"      .= String "WildHole"
    , "position"  .= n
    ]
  toJSON (IdPart name) = object
    [ "kind"      .= String "IdPart"
    , "rawName"   .= name
    ]

instance ToJSON NotationKind where
  toJSON InfixNotation    = String "InfixNotation"
  toJSON PrefixNotation   = String "PrefixNotation"
  toJSON PostfixNotation  = String "PostfixNotation"
  toJSON NonfixNotation   = String "NonfixNotation"
  toJSON NoNotation       = String "NoNotation"
