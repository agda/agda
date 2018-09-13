{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Abstract

module Agda.Interaction.JSON.Syntax.Abstract where

import Data.Aeson

import Agda.Interaction.JSON.Syntax.Concrete.Name
import {-# SOURCE #-} Agda.Interaction.JSON.Syntax.Fixity
import Agda.Interaction.JSON.Syntax.Position
import Agda.Interaction.JSON.Utils

import Agda.Syntax.Abstract

--------------------------------------------------------------------------------
-- Agda.Syntax.Abstract.Name

instance ToJSON Name where
  toJSON (Name name concrete bindingSite fixity) = object
    [ "id"          .= name
    , "concrete"    .= concrete
    , "bindingSite" .= bindingSite
    , "fixity"      .= fixity
    ]

instance ToJSON QName where
  toJSON (QName moduleName name) = object
    [ "module"  .= moduleName
    , "name"    .= name
    ]

instance ToJSON ModuleName where
  toJSON (MName names) = toJSON names
