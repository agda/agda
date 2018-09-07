{-# LANGUAGE OverloadedStrings #-}

-- | Encoding stuff into JSON values in TCM

module Agda.Interaction.JSON.Encode where

import Control.Monad (sequence, liftM2)
import Data.Aeson
import Data.Aeson.Types (Pair)
import Data.Text (Text)

import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C
import Agda.Syntax.Translation.InternalToAbstract as I2A

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

data TermRep = TermRep
  { internal :: I.Term
  , concrete :: C.Expr
  }

repTerm :: I.Term -> TCM TermRep
repTerm term = do
  concrete <- I2A.reify term >>= A2C.abstractToConcrete_
  return $ TermRep
    { concrete = concrete
    , internal = term
    }
