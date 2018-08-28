{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax

module Agda.Interaction.JSON.Syntax where

import Data.Aeson hiding (Result(..))

import Agda.Interaction.JSON.Encoding
import Agda.Interaction.JSON.Utils

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract     as A
import qualified Agda.Syntax.Concrete     as C
import qualified Agda.Syntax.Fixity       as F
import qualified Agda.Syntax.Notation     as N
import qualified Agda.Syntax.Position     as P

--------------------------------------------------------------------------------
-- Agda.Syntax.Common

instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

instance ToJSON FreeVariables where
  toJSON UnknownFVs       = Null
  toJSON (KnownFVs vars)  = toJSON vars

instance ToJSON Modality where
  toJSON (Modality relevance quantity) = object
    [ "relevance" .= relevance
    , "quantity"  .= quantity
    ]

instance ToJSON Quantity where
  toJSON Quantity0  = String "Quantity0"
  toJSON Quantityω  = String "Quantityω"

instance ToJSON Relevance where
  toJSON Relevant   = String "Relevant"
  toJSON NonStrict  = String "NonStrict"
  toJSON Irrelevant = String "Irrelevant"

instance ToJSON Overlappable where
  toJSON YesOverlap = String "YesOverlap"
  toJSON NoOverlap  = String "NoOverlap"

instance ToJSON Hiding where
  toJSON Hidden     = object [ "kind" .= String "Hidden" ]
  toJSON NotHidden  = object [ "kind" .= String "NotHidden" ]
  toJSON (Instance overlappable) = object
    [ "kind"          .= String "Instance"
    , "overlappable"  .= overlappable
    ]

instance ToJSON Origin where
  toJSON UserWritten  = String "UserWritten"
  toJSON Inserted     = String "Inserted"
  toJSON Reflected    = String "Reflected"
  toJSON CaseSplit    = String "CaseSplit"
  toJSON Substitution = String "Substitution"

instance ToJSON ArgInfo where
  toJSON (ArgInfo hiding modality origin freeVars) = object
    [ "hiding"    .= hiding
    , "modality"  .= modality
    , "origin"    .= origin
    , "freeVars"  .= freeVars
    ]

instance ToJSON NameId where
  toJSON (NameId name modul) = object
    [ "name"    .= name
    , "module"  .= modul
    ]

instance ToJSON a => ToJSON (Ranged a) where
  toJSON (Ranged range payload) = object
    [ "range"   .= range
    , "payload" .= payload
    ]

instance (ToJSON name, ToJSON a) => ToJSON (Named name a) where
  toJSON (Named name payload) = object
    [ "name"    .= name
    , "payload" .= payload
    ]

instance ToJSON a => ToJSON (Arg a) where
  toJSON (Arg argInfo unArg) = object
    [ "argInfo" .= argInfo
    , "payload" .= unArg
    ]

instance ToJSON DataOrRecord where
  toJSON IsData   = String "IsData"
  toJSON IsRecord = String "IsRecord"

--------------------------------------------------------------------------------
-- Agda.Syntax.Abstract

instance ToJSON A.Name where
  toJSON (A.Name name concrete bindingSite fixity) = object
    [ "id"          .= name
    , "concrete"    .= concrete
    , "bindingSite" .= bindingSite
    , "fixity"      .= fixity
    ]

instance ToJSONKey A.QName
instance ToJSON A.QName where
  toJSON (A.QName moduleName name) = object
    [ "module"  .= moduleName
    , "name"    .= name
    ]

instance ToJSONKey A.ModuleName where
instance ToJSON A.ModuleName where
  toJSON (A.MName names) = toJSON names

--------------------------------------------------------------------------------
-- Agda.Syntax.Concrete

instance ToJSON C.NamePart where
  toJSON C.Hole = Null
  toJSON (C.Id name) = toJSON name

instance ToJSONKey C.Name
instance ToJSON C.Name where
  toJSON (C.Name   range parts) = object
    [ "kind"  .= String "Name"
    , "range" .= range
    , "parts" .= parts
    ]
  toJSON (C.NoName range name) = object
    [ "kind"  .= String "NoName"
    , "range" .= range
    , "name"  .= name
    ]

instance ToJSONKey C.QName
instance ToJSON C.QName where
  toJSON (C.QName name) = object
    [ "kind"  .= String "QName"
    , "name"  .= name
    ]
  toJSON (C.Qual name qname) = object
    [ "kind"      .= String "Qual"
    , "name"      .= name
    , "namespace" .= qname
    ]

--------------------------------------------------------------------------------
-- Agda.Syntax.Fixity

instance ToJSON F.NotationSection where
  toJSON (F.NotationSection notation kind level isSection) = object
    [ "kind"      .= kind
    , "notation"  .= notation
    , "level"     .= level
    , "isSection" .= isSection
    ]

instance ToJSON F.NewNotation where
  toJSON (F.NewNotation name names fixity notation isOperator) = object
    [ "name"        .= name
    , "names"       .= names
    , "fixity"      .= fixity
    , "notation"    .= notation
    , "isOperator"  .= isOperator
    ]

instance ToJSON F.PrecedenceLevel where
  toJSON F.Unrelated = Null
  toJSON (F.Related n) = toJSON n

instance ToJSON F.Associativity where
  toJSON F.NonAssoc = String "NonAssoc"
  toJSON F.LeftAssoc = String "LeftAssoc"
  toJSON F.RightAssoc = String "RightAssoc"

instance ToJSON F.Fixity where
  toJSON (F.Fixity range level assoc) = object
    [ "range" .= range
    , "level" .= level
    , "assoc" .= assoc
    ]

instance ToJSON F.Fixity' where
  toJSON (F.Fixity' fixity notation range) = object
    [ "fixity"    .= fixity
    , "notation"  .= notation
    , "range"     .= range
    ]

--------------------------------------------------------------------------------
-- Agda.Syntax.Notation

instance ToJSON N.GenPart where
  toJSON (N.BindHole n) = object
    [ "kind"      .= String "BindHole"
    , "position"  .= n
    ]
  toJSON (N.NormalHole n) = object
    [ "kind"      .= String "NormalHole"
    , "position"  .= n
    ]
  toJSON (N.WildHole n) = object
    [ "kind"      .= String "WildHole"
    , "position"  .= n
    ]
  toJSON (N.IdPart name) = object
    [ "kind"      .= String "IdPart"
    , "rawName"   .= name
    ]

instance ToJSON N.NotationKind where
  toJSON N.InfixNotation    = String "InfixNotation"
  toJSON N.PrefixNotation   = String "PrefixNotation"
  toJSON N.PostfixNotation  = String "PostfixNotation"
  toJSON N.NonfixNotation   = String "NonfixNotation"
  toJSON N.NoNotation       = String "NoNotation"

--------------------------------------------------------------------------------
-- Agda.Syntax.Position
instance ToJSON a => ToJSON (P.Position' a) where
  toJSON (P.Pn src pos line col) = toJSON
    [ toJSON line, toJSON col, toJSON pos, toJSON src ]

instance ToJSON a => ToJSON (P.Interval' a) where
  toJSON (P.Interval start end) = toJSON [toJSON start, toJSON end]

instance ToJSON a => ToJSON (P.Range' a) where
  toJSON (P.Range src is) = object
    [ "kind" .= String "Range"
    , "source" .= src
    , "intervals" .= is
    ]
  toJSON P.NoRange = object
    [ "kind" .= String "NoRange" ]
