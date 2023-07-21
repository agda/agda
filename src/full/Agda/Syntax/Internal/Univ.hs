{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE DeriveAnyClass             #-}

-- | Kinds of standard universes: @Prop@, @Type@, @SSet@.

module Agda.Syntax.Internal.Univ where

import Control.DeepSeq ( NFData  )
import GHC.Generics    ( Generic )

import Agda.Utils.Boolean

-- * Types
---------------------------------------------------------------------------

-- | Flavor of standard universe (@Prop < Type < SSet@,).
data Univ
  = UProp  -- ^ Fibrant universe of propositions.
  | UType  -- ^ Fibrant universe.
  | USSet  -- ^ Non-fibrant universe.
  deriving stock (Eq, Ord, Show, Bounded, Enum, Generic)
  deriving anyclass NFData
    -- NB: for deriving Ord, keep ordering UProp < UType < USSet!

-- | We have @IsFibrant < IsStrict@.
data IsFibrant
  = IsFibrant  -- ^ Fibrant universe.
  | IsStrict   -- ^ Non-fibrant universe.
  deriving (Show, Eq, Ord, Generic)
    -- NB: for deriving Ord, keep ordering IsFibrant < IsStrict!

instance Boolean IsFibrant where
  fromBool = \case
    True -> IsFibrant
    False -> IsStrict

instance IsBool IsFibrant where
  toBool = \case
    IsFibrant -> True
    IsStrict -> False

-- * Universe kind arithmetic
---------------------------------------------------------------------------

-- | The successor universe type of a universe.
univUniv :: Univ -> Univ
univUniv = \case
  UProp -> UType
  UType -> UType
  USSet -> USSet

-- | Compute the universe type of a function space from the universe types of domain and codomain.
funUniv :: Univ -> Univ -> Univ
funUniv = curry $ \case
  (USSet, _) -> USSet
  (_, USSet) -> USSet
  (_, u)     -> u

-- ** Inverting 'funUniv'

-- | Conclude @u1@ from @funUniv u1 u2@ and @u2@.

domainUniv ::
      Bool       -- ^ Have 'UProp'?
   -> Univ       -- ^ 'Univ' kind of the 'funSort'.
   -> Univ       -- ^ 'Univ' kind of the codomain.
   -> Maybe Univ -- ^ 'Univ' kind of the domain, if unique.
domainUniv propEnabled u = \case
  USSet -> Nothing
  _  | u == USSet  -> Just USSet
     | propEnabled -> Nothing
     | otherwise   -> Just UType

-- | Conclude @u2@ from @funUniv u1 u2@ and @u1@.

codomainUniv ::
      Univ       -- ^ 'Univ' kind of the 'funSort'.
   -> Univ       -- ^ 'Univ' kind of the domain.
   -> Maybe Univ -- ^ 'Univ' kind of the codomain, if uniquely exists.
codomainUniv u = \case
  USSet -> Nothing
  _ -> Just u

-- * Fibrancy

-- | Fibrancy of standard universes.

univFibrancy :: Univ -> IsFibrant
univFibrancy = \case
  UProp -> IsFibrant
  UType -> IsFibrant
  USSet -> IsStrict

-- * Printing

-- | Hacky showing of standard universes, does not take actual names into account.

showUniv :: Univ -> String
showUniv = \case
  UProp -> "Prop"
  UType -> "Set"
  USSet -> "SSet"
