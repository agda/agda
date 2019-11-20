{-# LANGUAGE OverloadedStrings #-}

-- | Encoding stuff into JSON values in TCM

module Agda.Interaction.JSON
  ( EncodeTCM(..)
  , obj, kind, kind'
  , (@=), (#=)
  , (>=>), (<=<)
  -- , ToRep(..), rep
  ) where

import Control.Monad ((>=>), (<=<), sequence, liftM2)
import Data.Aeson
import Data.Aeson.Types (Pair)
import Data.Text (Text)
import GHC.Int (Int32)

-- import qualified Agda.Syntax.Translation.InternalToAbstract as I2A
-- import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C

-- import qualified Agda.Syntax.Concrete as C
-- import qualified Agda.Syntax.Internal as I
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
  encodeTCM = pure . toJSON

-- | TCM monadic version of object
obj :: [TCM Pair] -> TCM Value
obj = (object <$>) . sequence

-- | Pairs a key with a value wrapped in TCM
(#=) :: (ToJSON a) => Text -> TCM a -> TCM Pair
(#=) key boxed = do
  value <- boxed
  pure $ key .= toJSON value

-- | Abbreviation of `_ #= encodeTCM _`
(@=) :: (EncodeTCM a) => Text -> a -> TCM Pair
(@=) key value = do
  encoded <- encodeTCM value
  pure $ key .= encoded

-- | A handy alternative of `obj` with kind specified
kind :: Text -> [TCM Pair] -> TCM Value
kind k = obj . (("kind" @= String k) :)

-- | A handy alternative of `object` with kind specified
kind' :: Text -> [Pair] -> Value
kind' k = object . (("kind" .= String k) :)

-- ---------------------------------------------------------------------------
-- -- * The Rep & ToRep class
--
-- -- | Translates internal types to concrete types
-- class ToRep i c | i -> c where
--   toRep :: i -> TCM c
--
-- instance ToRep I.Term C.Expr where
--   toRep internal = I2A.reify internal >>= A2C.abstractToConcrete_
--
-- instance ToRep I.Type C.Expr where
--   toRep internal = I2A.reify internal >>= A2C.abstractToConcrete_
--
-- data Rep internal concrete = Rep
--   { internalRep :: internal
--   , concreteRep :: concrete
--   }
--
-- instance (ToJSON i, ToJSON c) => ToJSON (Rep i c) where
--   toJSON (Rep i c) = object
--     [ "internal" .= i
--     , "concrete" .= c
--     ]
--
-- rep :: (ToRep i c) => i -> TCM (Rep i c)
-- rep internal = do
--   concrete <- toRep internal
--   return $ Rep
--     { internalRep = internal
--     , concreteRep = concrete
--     }

--------------------------------------------------------------------------------
-- Instances of ToJSON or EncodeTCM

encodeListTCM :: EncodeTCM a => [a] -> TCM Value
encodeListTCM = mapM encodeTCM >=> return . toJSONList

instance EncodeTCM a => EncodeTCM [a] where
  encodeTCM = mapM encodeTCM >=> return . toJSONList

-- overlaps with the instance declared above
instance {-# OVERLAPPING #-} EncodeTCM String

instance EncodeTCM Bool where
instance EncodeTCM Int where
instance EncodeTCM Int32 where
instance EncodeTCM Value where
instance EncodeTCM Doc where

instance ToJSON Doc where
  toJSON = toJSON . render

instance EncodeTCM a => EncodeTCM (Maybe a) where
  encodeTCM Nothing   = return Null
  encodeTCM (Just a)  = encodeTCM a

instance ToJSON File.AbsolutePath where
  toJSON (File.AbsolutePath path) = toJSON path

instance ToJSON a => ToJSON (Strict.Maybe a) where
  toJSON (Strict.Just a) = toJSON a
  toJSON Strict.Nothing  = Null
