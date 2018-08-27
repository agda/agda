{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax

module Agda.Interaction.JSON.Syntax where

import Data.Aeson hiding (Result(..))

import Agda.Interaction.JSON.Encoding
import Agda.Syntax.Common
import qualified Agda.Syntax.Position as P

--------------------------------------------------------------------------------
-- Common

instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

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
