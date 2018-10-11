{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Internal

module Agda.Interaction.JSON.Syntax.Translation where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Concrete

import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.InternalToAbstract

--------------------------------------------------------------------------------
-- | Instances of EncodeTCM

instance EncodeTCM NamedClause where
  encodeTCM = reify >=> abstractToConcrete_ >=> encodeTCM

instance EncodeTCM RangeAndPragma where
  encodeTCM = abstractToConcrete_ >=> encodeTCM
