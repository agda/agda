{-# LANGUAGE OverloadedStrings #-}

-- | Encoding stuff into JSON values in TCM

module Agda.Interaction.JSON.Encode where

import Control.Monad (sequence, liftM2)
import Data.Aeson
import Data.Aeson.Types (Pair)
import Data.Text (Text)

import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C
import qualified Agda.Syntax.Translation.InternalToAbstract as I2A

import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (PrettyTCM(..))
import Agda.Utils.Pretty

---------------------------------------------------------------------------
-- * The EncodeTCM class

-- | The JSON version of`PrettyTCM`, for encoding JSON value in TCM
class EncodeTCM a where
  encodeTCM :: a -> TCM Value
  default encodeTCM :: ToJSON a => a -> TCM Value
  encodeTCM = return . toJSON

instance ToJSON Doc where
  toJSON = toJSON . render

-- | TCM monadic version of object
obj :: [TCM Pair] -> TCM Value
obj pairs = object <$> sequence pairs

-- | TCM monadic version of (.=)
(@=) :: (ToJSON a) => Text -> a -> TCM Pair
(@=) key value = return (key .= toJSON value)

-- | Pairs a key with a value wrapped in TCM
(#=) :: (ToJSON a) => Text -> TCM a -> TCM Pair
(#=) key boxed = do
  value <- boxed
  return (key .= toJSON value)

---------------------------------------------------------------------------
-- * The Rep & ToRep class

-- | Translates internal types to concrete types
class ToRep i c | i -> c where
  toRep :: i -> TCM c

instance ToRep I.Term C.Expr where
  toRep internal = I2A.reify internal >>= A2C.abstractToConcrete_

instance ToRep I.Type C.Expr where
  toRep internal = I2A.reify internal >>= A2C.abstractToConcrete_

data Rep internal concrete = Rep
  { internalRep :: internal
  , concreteRep :: concrete
  }

instance (ToJSON i, ToJSON c) => ToJSON (Rep i c) where
  toJSON (Rep i c) = object
    [ "internal" .= i
    , "concrete" .= c
    ]

rep :: (ToRep i c) => i -> TCM (Rep i c)
rep internal = do
  concrete <- toRep internal
  return $ Rep
    { internalRep = internal
    , concreteRep = concrete
    }
