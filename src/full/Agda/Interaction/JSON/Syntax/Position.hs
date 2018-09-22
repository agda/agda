{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Position

module Agda.Interaction.JSON.Syntax.Position where

import Data.Aeson

import Agda.Syntax.Position

instance ToJSON a => ToJSON (Position' a) where
  toJSON (Pn _ pos line col) = toJSON
    [ toJSON line, toJSON col, toJSON pos ]

instance ToJSON a => ToJSON (Interval' a) where
  toJSON (Interval start end) = object
    [ "start" .= start
    , "end"   .= end
    ]

instance ToJSON a => ToJSON (Range' a) where
  toJSON (Range src is) = object
    [ "kind"      .= String "Range"
    , "intervals" .= is
    , "source"    .= src
    ]
  toJSON NoRange = object
    [ "kind"      .= String "NoRange"
    ]
