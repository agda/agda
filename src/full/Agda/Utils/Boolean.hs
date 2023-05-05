-- | Boolean algebras and types isomorphic to 'Bool'.
--
-- There are already solutions for 'Boolean' algebras in the Haskell ecosystem,
-- but they do not offer easy instantiations for types isomorphic to 'Bool'.
-- In particular, if type @a@ is isomorphic to 'Bool', so it satisfies `IsBool a`,
-- we would like to instantiate 'Boolean a' by just giving 'true' and 'false'.
-- To facilitate this within the limits of the Haskell class system,
-- we define the class 'Boolean' mutually with class 'IsBool',
-- so that operations 'not', '(&&)', and '(||)' can get default implementations.
--
-- Usage:
-- @
--    import Prelude hiding ( not, (&&), (||) )
--    import Agda.Utils.Boolean
-- @

module Agda.Utils.Boolean where

import Prelude ( Bool(True,False), Eq, ($), (.), const, id )
import qualified Prelude as P

infixr 3 &&
infixr 2 ||

-- | Boolean algebras.
--
class Boolean a where
  fromBool :: Bool -> a

  true :: a
  true = fromBool True

  false :: a
  false = fromBool False

  not :: a -> a

  (&&) :: a -> a -> a

  (||) :: a -> a -> a

  implies :: a -> a -> a
  implies a b = b || not a

  -- | Set difference, dual to 'implies'.
  butNot :: a -> a -> a
  butNot a b = a && not b

  default not :: IsBool a => a -> a
  not = fromBool1 P.not

  default (&&) :: IsBool a => a -> a -> a
  (&&) = fromBool2 (P.&&)

  default (||) :: IsBool a => a -> a -> a
  (||) = fromBool2 (P.||)

-- | Types isomorphic to 'Bool'.
--
class (Boolean a, Eq a) => IsBool a where
  toBool :: a -> Bool

  ifThenElse :: a -> b -> b -> b
  ifThenElse c t e = if toBool c then t else e

  fromBool1 :: (Bool -> Bool) -> (a -> a)
  fromBool1 f = fromBool . f . toBool

  fromBool2 :: (Bool -> Bool -> Bool) -> (a -> a -> a)
  fromBool2 f a b = fromBool $ f (toBool a) (toBool b)

  {-# MINIMAL toBool #-}

instance Boolean Bool where
  fromBool = id

instance IsBool Bool where
  toBool = id
  -- optional
  fromBool1 = id
  fromBool2 = id

instance Boolean b => Boolean (a -> b) where
  fromBool   = const . fromBool
  not f      = not . f
  (f && g) a = f a && g a
  (f || g) a = f a || g a
