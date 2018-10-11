{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Notation

module Agda.Interaction.JSON.Syntax.Notation where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Common
import Agda.Syntax.Notation


--------------------------------------------------------------------------------

instance ToJSON GenPart where
  toJSON (BindHole n) = kind' "BindHole"
    [ "position"  .= n
    ]
  toJSON (NormalHole n) = kind' "NormalHole"
    [ "position"  .= n
    ]
  toJSON (WildHole n) = kind' "WildHole"
    [ "position"  .= n
    ]
  toJSON (IdPart name) = kind' "IdPart"
    [ "rawName"   .= name
    ]

instance ToJSON NotationKind where
  toJSON InfixNotation    = String "InfixNotation"
  toJSON PrefixNotation   = String "PrefixNotation"
  toJSON PostfixNotation  = String "PostfixNotation"
  toJSON NonfixNotation   = String "NonfixNotation"
  toJSON NoNotation       = String "NoNotation"
