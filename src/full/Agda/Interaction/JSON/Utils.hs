{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Utils

module Agda.Interaction.JSON.Utils where

import Data.Aeson

import Agda.Interaction.JSON.Encoding

import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.FileName as File


instance EncodeTCM a => EncodeTCM (Maybe a) where
  encodeTCM Nothing   = return Null
  encodeTCM (Just a)  = encodeTCM a

--------------------------------------------------------------------------------
-- FileName

instance ToJSON File.AbsolutePath where
  toJSON (File.AbsolutePath path) = toJSON path

--------------------------------------------------------------------------------
-- Maybe.Strict


instance ToJSON a => ToJSON (Strict.Maybe a) where
  toJSON (Strict.Just a) = toJSON a
  toJSON Strict.Nothing = Null
