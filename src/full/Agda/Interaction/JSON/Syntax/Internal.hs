{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Internal

module Agda.Interaction.JSON.Syntax.Internal where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Common
import Agda.Interaction.JSON.Syntax.Abstract
import Agda.Interaction.JSON.Syntax.Concrete
import Agda.Interaction.JSON.Syntax.Literal
import Agda.Syntax.Internal
import qualified Agda.Syntax.Translation.InternalToAbstract as I2A
import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C

--------------------------------------------------------------------------------
-- Agda.Syntax.Internal

instance EncodeTCM Term where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM Elim where
  encodeTCM (Apply arg) = kind "Apply"
    [ "arg"         @= arg
    ]
  encodeTCM (Proj origin name) = kind "Proj"
    [ "projOrigin"  @= origin
    , "name"        @= name
    ]
  encodeTCM (IApply x y r) = kind "IApply"
    [ "endpoint1"   @= x
    , "endpoint2"   @= y
    , "endpoint3"   @= r
    ]

instance EncodeTCM Type where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM Telescope where
  encodeTCM tel' = do
      tel <- I2A.reify tel'
      A2C.runAbsToCon (A2C.bindToConcrete tel (return . concat)) >>= encodeTCM

instance EncodeTCM Sort where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM

instance EncodeTCM Level where
  encodeTCM = I2A.reify >=> A2C.abstractToConcrete_ >=> encodeTCM
