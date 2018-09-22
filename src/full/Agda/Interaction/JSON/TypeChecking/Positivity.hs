{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.TypeChecking.Positivity

module Agda.Interaction.JSON.TypeChecking.Positivity where

import Data.Aeson
import Data.Foldable (toList)

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Abstract.Name
-- import Agda.Interaction.JSON.Syntax.Concrete.Name
import Agda.Interaction.JSON.Syntax.Position
import Agda.TypeChecking.Positivity.Occurrence
import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C

--------------------------------------------------------------------------------

instance EncodeTCM OccursWhere where
  encodeTCM Unknown = obj
    [ "kind"        @= String "Unknown"
    ]
  encodeTCM (Known range wheres) = obj
    [ "kind"        @= String "Known"
    , "range"       @= range
    , "wheres"      #= mapM encodeTCM (toList wheres)
    ]

instance EncodeTCM Where where
  encodeTCM LeftOfArrow = obj
    [ "kind"        @= String "LeftOfArrow"
    ]
  encodeTCM (DefArg name n) = obj
    [ "kind"        @= String "DefArg"
    , "name"        #= A2C.abstractToConcrete_ name
    , "index"       @= n
    ]
  encodeTCM UnderInf = obj
    [ "kind"        @= String "UnderInf"
    ]
  encodeTCM VarArg = obj
    [ "kind"        @= String "VarArg"
    ]
  encodeTCM MetaArg = obj
    [ "kind"        @= String "MetaArg"
    ]
  encodeTCM (ConArgType name) = obj
    [ "kind"        @= String "ConArgType"
    , "name"        #= A2C.abstractToConcrete_ name
    ]
  encodeTCM (IndArgType name) = obj
    [ "kind"        @= String "IndArgType"
    , "name"        #= A2C.abstractToConcrete_ name
    ]
  encodeTCM (InClause n) = obj
    [ "kind"        @= String "InClause"
    , "index"       @= n
    ]
  encodeTCM Matched = obj
    [ "kind"        @= String "Matched"
    ]
  encodeTCM (InDefOf name) = obj
    [ "kind"        @= String "InDefOf"
    , "name"        #= A2C.abstractToConcrete_ name
    ]


instance ToJSON Occurrence where
  toJSON Mixed      = String "Mixed"
  toJSON JustNeg    = String "JustNeg"
  toJSON JustPos    = String "JustPos"
  toJSON StrictPos  = String "StrictPos"
  toJSON GuardPos   = String "GuardPos"
  toJSON Unused     = String "Unused"
