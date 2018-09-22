{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Abstract.Name

module Agda.Interaction.JSON.Syntax.Abstract.Name where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Concrete.Name
import {-# SOURCE #-} Agda.Interaction.JSON.Syntax.Fixity
import Agda.Interaction.JSON.Syntax.Position

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Translation.InternalToAbstract as I2A
import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C

--------------------------------------------------------------------------------
-- Agda.Syntax.Abstract.Name

instance EncodeTCM Name where
    encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance ToJSON Name where
  toJSON (Name name concrete bindingSite fixity) = object
    [ "id"          .= name
    , "concrete"    .= concrete
    , "bindingSite" .= bindingSite
    , "fixity"      .= fixity
    ]

instance EncodeTCM QName where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance ToJSON QName where
  toJSON (QName moduleName name) = object
    [ "module"  .= moduleName
    , "name"    .= name
    ]

instance EncodeTCM ModuleName where
  encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM

instance ToJSON ModuleName where
  toJSON (MName names) = toJSON names
--
-- --------------------------------------------------------------------------------
--
-- instance EncodeTCM Pattern where
--   encodeTCM = A2C.abstractToConcrete_ >=> encodeTCM
