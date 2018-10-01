{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.Syntax.Internal

module Agda.Interaction.JSON.Syntax.Internal where

import Data.Aeson

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Abstract.Name
import Agda.Interaction.JSON.Syntax.Common
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
  encodeTCM (IApply _ _ v) = encodeTCM v
  encodeTCM (Apply v) = encodeTCM v
  encodeTCM (Proj _ f)= encodeTCM f

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
