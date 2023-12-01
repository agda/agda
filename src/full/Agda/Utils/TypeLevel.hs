{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeOperators        #-}

-- We need undecidable instances for the definition of @Foldr@,
-- and @Domains@ and @CoDomain@ using @If@ for instance.
{-# LANGUAGE UndecidableInstances #-}

module Agda.Utils.TypeLevel where

import Data.Kind ( Type )
import Data.Proxy
import GHC.Exts (Constraint)

------------------------------------------------------------------
-- CONSTRAINTS
------------------------------------------------------------------

-- | @All p as@ ensures that the constraint @p@ is satisfied by
--   all the 'types' in @as@.
--   (Types is between scare-quotes here because the code is
--   actually kind polymorphic)

type family All (p :: k -> Constraint) (as :: [k]) :: Constraint where
  All p '[]       = ()
  All p (a ': as) = (p a, All p as)

------------------------------------------------------------------
-- FUNCTIONS
-- Type-level and Kind polymorphic versions of usual value-level
-- functions.
------------------------------------------------------------------

-- | On Booleans
type family If (b :: Bool) (l :: k) (r :: k) :: k where
  If 'True  l r = l
  If 'False l r = r

-- | On Lists
type family Foldr (c :: k -> l -> l) (n :: l) (as :: [k]) :: l where
  Foldr c n '[]       = n
  Foldr c n (a ': as) = c a (Foldr c n as)

-- | Version of @Foldr@ taking a defunctionalised argument so
--   that we can use partially applied functions.
type family Foldr' (c :: Function k (Function l l -> Type) -> Type)
                   (n :: l) (as :: [k]) :: l where
  Foldr' c n '[]       = n
  Foldr' c n (a ': as) = Apply (Apply c a) (Foldr' c n as)

type family Map (f :: Function k l -> Type) (as :: [k]) :: [l] where
  Map f as = Foldr' (ConsMap0 f) '[] as

data ConsMap0 :: (Function k l -> Type) -> Function k (Function [l] [l] -> Type) -> Type
data ConsMap1 :: (Function k l -> Type) -> k -> Function [l] [l] -> Type
type instance Apply (ConsMap0 f)    a = ConsMap1 f a
type instance Apply (ConsMap1 f a) tl = Apply f a ': tl

type family Constant (b :: l) (as :: [k]) :: [l] where
  Constant b as = Map (Constant1 b) as

------------------------------------------------------------------
-- TYPE FORMERS
------------------------------------------------------------------

-- | @Arrows [a1,..,an] r@ corresponds to @a1 -> .. -> an -> r@
-- | @Products [a1,..,an]@ corresponds to @(a1, (..,( an, ())..))@

type Arrows   (as :: [Type]) (r :: Type) = Foldr (->) r as
type Products (as :: [Type])             = Foldr (,) () as

data StrictPair a b = Pair a b
type StrictProducts (as :: [Type]) = Foldr StrictPair () as

strictCurry :: (StrictPair a b -> c) -> (a -> b -> c)
strictCurry f = \ !a !b -> f (Pair a b)
{-# INLINE strictCurry #-}

strictUncurry :: (a -> b -> c) -> (StrictPair a b -> c)
strictUncurry f = \ !(Pair a b) -> f a b
{-# INLINE strictUncurry #-}

-- | @IsBase t@ is @'True@ whenever @t@ is *not* a function space.

type family IsBase (t :: Type) :: Bool where
  IsBase (a -> t) = 'False
  IsBase a        = 'True

-- | Using @IsBase@ we can define notions of @Domains@ and @CoDomains@
--   which *reduce* under positive information @IsBase t ~ 'True@ even
--   though the shape of @t@ is not formally exposed

type family Domains (t :: Type) :: [Type] where
  Domains t = If (IsBase t) '[] (Domains' t)
type family Domains' (t :: Type) :: [Type] where
  Domains' (a -> t) = a ': Domains t

type family CoDomain (t :: Type) :: Type where
  CoDomain t = If (IsBase t) t (CoDomain' t)
type family CoDomain' (t :: Type) :: Type where
  CoDomain' (a -> t) = CoDomain t

------------------------------------------------------------------
-- TYPECLASS MAGIC
------------------------------------------------------------------

-- | @Currying as b@ witnesses the isomorphism between @Arrows as b@
--   and @Products as -> b@. It is defined as a type class rather
--   than by recursion on a singleton for @as@ so all of that these
--   conversions are inlined at compile time for concrete arguments.

class Currying as b where
  uncurrys :: Proxy as -> Proxy b -> Arrows as b -> Products as -> b
  currys   :: Proxy as -> Proxy b -> (Products as -> b) -> Arrows as b

instance Currying '[] b where
  uncurrys _ _ f = \ () -> f
  currys   _ _ f = f ()

instance Currying as b => Currying (a ': as) b where
  uncurrys _ p f = uncurry $ uncurrys (Proxy :: Proxy as) p . f
  currys   _ p f = currys (Proxy :: Proxy as) p . curry f


class StrictCurrying as b where
  strictUncurrys :: Proxy as -> Proxy b -> Arrows as b -> StrictProducts as -> b
  strictCurrys   :: Proxy as -> Proxy b -> (StrictProducts as -> b) -> Arrows as b

instance StrictCurrying '[] b where
  strictUncurrys _ _ f = \ () -> f; {-# INLINE strictUncurrys #-}
  strictCurrys   _ _ f = f ();      {-# INLINE strictCurrys #-}

instance StrictCurrying as b => StrictCurrying (a ': as) b where
  strictUncurrys _ p f = strictUncurry $ strictUncurrys (Proxy :: Proxy as) p . f
  {-# INLINE strictUncurrys #-}
  strictCurrys   _ p f = strictCurrys (Proxy :: Proxy as) p . strictCurry f
  {-# INLINE strictCurrys #-}

------------------------------------------------------------------
-- DEFUNCTIONALISATION
-- Cf. Eisenberg and Stolarek's paper:
-- Promoting Functions to Type Families in Haskell
------------------------------------------------------------------

data Function :: Type -> Type -> Type

data Constant0 :: Function a (Function b a -> Type) -> Type
data Constant1 :: Type -> Function b a -> Type

type family Apply (t :: Function k l -> Type) (u :: k) :: l

type instance Apply Constant0     a = Constant1 a
type instance Apply (Constant1 a) b = a
