{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.TypeChecking

module Agda.Interaction.JSON.TypeChecking where

import Data.Aeson

import Agda.Interaction.JSON.Encoding
import Agda.Interaction.JSON.Syntax
import Agda.Interaction.JSON.Utils
import Agda.Syntax.Position (Range, Range'(..))

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors

import Agda.Utils.Pretty (render)

--------------------------------------------------------------------------------

instance EncodeTCM TCErr where
  encodeTCM (TypeError _ closure) = obj
    [ "kind"      @= String "TypeError"
    , "range"     @= envRange (clEnv closure)
    , "typeError" #= encodeTCM (clValue closure)
    ]
  encodeTCM (Exception range doc) = obj
    [ "kind"        @= String "Exception"
    , "range"       @= range
    , "description" @= toJSON (render doc)
    ]
  encodeTCM (IOException _ range exception) = obj
    [ "kind"        @= String "IOException"
    , "range"       @= range
    , "exception"   @= toJSON (show exception)
    ]
  encodeTCM PatternErr = obj
    [ "kind"        @= String "PatternErr"
    , "range"       @= (NoRange :: Range)
    ]

--------------------------------------------------------------------------------

instance EncodeTCM TypeError where
  encodeTCM err = obj
    [ "kind" @= toJSON (errorString err)
    ]
