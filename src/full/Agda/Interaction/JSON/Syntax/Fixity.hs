{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Fixity

module Agda.Interaction.JSON.Syntax.Fixity where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Abstract.Name
import Agda.Interaction.JSON.Syntax.Concrete.Name
import Agda.Interaction.JSON.Syntax.Position
import Agda.Interaction.JSON.Syntax.Notation

import Agda.Syntax.Fixity

--------------------------------------------------------------------------------

instance ToJSON Fixity' where
  toJSON (Fixity' fixity notation range) = object
    [ "fixity"    .= fixity
    , "notation"  .= notation
    , "range"     .= range
    ]

instance ToJSON NewNotation where
  toJSON (NewNotation name names fixity notation isOperator) = object
    [ "name"        .= name
    , "names"       .= names
    , "fixity"      .= fixity
    , "notation"    .= notation
    , "isOperator"  .= isOperator
    ]


instance EncodeTCM NotationSection where
instance ToJSON NotationSection where
  toJSON (NotationSection notation kind level isSection) = object
    [ "notation"  .= notation
    , "kind"      .= kind
    , "level"     .= level
    , "isSection" .= isSection
    ]

instance ToJSON PrecedenceLevel where
  toJSON Unrelated = Null
  toJSON (Related n) = toJSON n

instance ToJSON Associativity where
  toJSON NonAssoc = String "NonAssoc"
  toJSON LeftAssoc = String "LeftAssoc"
  toJSON RightAssoc = String "RightAssoc"

instance ToJSON Fixity where
  toJSON (Fixity range level assoc) = object
    [ "range" .= range
    , "level" .= level
    , "assoc" .= assoc
    ]
