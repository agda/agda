{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax

module Agda.Interaction.JSON.Syntax where

import Data.Aeson hiding (Result(..))

import Agda.Interaction.JSON.Encoding
import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Position as P

--------------------------------------------------------------------------------
-- Abstract

-- kindOfPattern :: Int
-- kindOfPattern arg = case arg of
--   A.VarP    {} -> String "variable"
--   A.ConP    {} -> String "constructor"
--   A.ProjP   {} -> __IMPOSSIBLE__
--   A.DefP    {} -> __IMPOSSIBLE__
--   A.WildP   {} -> String "wildcard"
--   A.DotP    {} -> String "dot"
--   A.AbsurdP {} -> String "absurd"
--   A.LitP    {} -> String "literal"
--   A.RecP    {} -> String "record"
--   A.WithP   {} -> String "with"
--   A.EqualP  {} -> String "equality"
--   A.AsP _ _ p -> kindOfPattern p
--   A.PatternSynP {} -> __IMPOSSIBLE__

--------------------------------------------------------------------------------
-- Common

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

instance ToJSON a => ToJSON (Arg a) where
  toJSON (Arg argInfo unArg) = object
    [ "argInfo" .= argInfo
    , "payload" .= unArg
    ]

instance ToJSON DataOrRecord where
  toJSON IsData   = String "IsData"
  toJSON IsRecord = String "IsRecord"

--------------------------------------------------------------------------------
-- Position
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
