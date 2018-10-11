{-# LANGUAGE OverloadedStrings #-}

-- | Encoding stuff into JSON values in TCM

module Agda.Interaction.JSON.Encode
  ( EncodeTCM(..)
  , obj, kind, kind'
  , (@=), (#=)
  , (>=>)
  , Precedence(..), encodeTCMCtx, encodeTCMTopCtx
  ) where

import Control.Monad ((>=>), sequence, liftM2)
import Data.Aeson
import Data.Aeson.Types (Pair)
import Data.Text (Text)
import Data.Vector (fromList)
import GHC.Int (Int32)
import GHC.Word (Word64)

import qualified Agda.Syntax.Translation.InternalToAbstract as I2A
import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C

import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Fixity (Precedence(..))
import Agda.Syntax.Scope.Monad (withContextPrecedence)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (PrettyTCM(..))
import Agda.Utils.Pretty
import qualified Agda.Utils.FileName as File
import qualified Agda.Utils.Maybe.Strict as Strict

---------------------------------------------------------------------------
-- * The EncodeTCM class

-- | The JSON version of`PrettyTCM`, for encoding JSON value in TCM
class EncodeTCM a where
  encodeTCM :: a -> TCM Value
  default encodeTCM :: ToJSON a => a -> TCM Value
  encodeTCM = return . toJSON

-- | Encode to JSON with a given context precedence
encodeTCMCtx :: EncodeTCM a => Precedence -> a -> TCM Value
encodeTCMCtx prec = withContextPrecedence prec . encodeTCM

encodeTCMTopCtx :: EncodeTCM a => a -> TCM Value
encodeTCMTopCtx = encodeTCMCtx TopCtx

-- | TCM monadic version of object
obj :: [TCM Pair] -> TCM Value
obj pairs = object <$> sequence pairs

-- | Pairs a key with a value wrapped in TCM
(#=) :: (ToJSON a) => Text -> TCM a -> TCM Pair
(#=) key boxed = do
  value <- boxed
  return (key .= toJSON value)

-- | Abbreviation of `_ #= encodeTCM _`
(@=) :: (EncodeTCM a) => Text -> a -> TCM Pair
(@=) key value = do
  encoded <- encodeTCM value
  return (key .= encoded)

-- | A handy alternative of `obj` with kind specified
kind :: Text -> [TCM Pair] -> TCM Value
kind k pairs = obj (("kind" @= String k) : pairs)

-- | A handy alternative of `object` with kind specified
kind' :: Text -> [Pair] -> Value
kind' k pairs = object (("kind" .= String k) : pairs)

--------------------------------------------------------------------------------
-- Instances of ToJSON or EncodeTCM

instance EncodeTCM a => EncodeTCM [a] where
  encodeTCM = mapM encodeTCM >=> return . Array . fromList

-- overlaps with the instance declared above
instance {-# OVERLAPPING #-} EncodeTCM String

instance EncodeTCM Char where
instance EncodeTCM Bool where
instance EncodeTCM Double where
instance EncodeTCM Int where
instance EncodeTCM Integer where
instance EncodeTCM Int32 where
instance EncodeTCM Word64 where

instance EncodeTCM Value where

instance EncodeTCM Doc where
instance ToJSON Doc where
  toJSON = toJSON . render

instance EncodeTCM a => EncodeTCM (Maybe a) where
  encodeTCM Nothing   = return Null
  encodeTCM (Just a)  = encodeTCM a

instance EncodeTCM File.AbsolutePath where
instance ToJSON File.AbsolutePath where
  toJSON (File.AbsolutePath path) = toJSON path

instance ToJSON a => ToJSON (Strict.Maybe a) where
  toJSON (Strict.Just a) = toJSON a
  toJSON Strict.Nothing  = Null
