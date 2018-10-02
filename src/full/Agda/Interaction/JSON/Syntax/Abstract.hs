{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Abstract

module Agda.Interaction.JSON.Syntax.Abstract where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Concrete

import Agda.Syntax.Abstract
import qualified Agda.Syntax.Translation.InternalToAbstract as I2A
import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C

--------------------------------------------------------------------------------
-- Names

instance EncodeTCM Name where
    encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM QName where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM ModuleName where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

--------------------------------------------------------------------------------

instance EncodeTCM Declaration where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM Pattern where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM Expr where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM Clause where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM SpineClause where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM LetBinding where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM
