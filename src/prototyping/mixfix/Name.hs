------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

module Name
  ( Assoc(..)
  , Fixity(..)
  , fixAssocInvariant
  , ignoreAssoc
  , Name(..)
  , isOperator
  , nameInvariant
  , name
  , operator
  , tests
  ) where

import Data.Function
import qualified Data.Maybe as Maybe
import Control.Monad
import Test.QuickCheck

import Utilities hiding (tests)

------------------------------------------------------------------------
-- Types

-- | Associativity.

data Assoc = Non | L | R
             deriving (Eq, Ord, Show)

-- | Fixity.

data Fixity = Prefix | Postfix | Infix
              deriving (Eq, Ord, Show)

-- | The associativity should always be 'Non' for non-infix operators.

fixAssocInvariant :: (Fixity, Assoc) -> Bool
fixAssocInvariant (Infix, _) = True
fixAssocInvariant (_, ass)   = ass == Non

-- | Ignores the associativity of non-infix operators.

ignoreAssoc :: Fixity -> Assoc -> (Fixity, Assoc)
ignoreAssoc Infix ass = (Infix, ass)
ignoreAssoc f     _   = (f,     Non)

prop_ignoreAssoc f a = fixAssocInvariant (ignoreAssoc f a)

-- | A name is a completely qualified name.

data Name = Name { moduleName :: [String]
                 , fixity     :: Maybe Fixity
                   -- ^ 'Just' something for operators.
                 , nameParts  :: [String]
                   -- ^ A /non-empty/ list of /non-empty/ name parts.
                   -- A singleton list for non-operators.
                 }
            deriving (Show, Eq, Ord)

-- | Is the name an operator?

isOperator :: Name -> Bool
isOperator = Maybe.isJust . fixity

-- | The name invariant.

nameInvariant n@(Name m f ns) =
  nonEmpty ns && all nonEmpty ns &&
  if isOperator n then True else length ns == 1
  where nonEmpty = not . null

------------------------------------------------------------------------
-- Test data generators

instance Arbitrary Assoc where
  arbitrary = elements [Non, L, R]

instance Arbitrary Fixity where
  arbitrary = elements [Prefix, Postfix, Infix]

-- | Generates a name with the given fixity.

name :: Maybe Fixity -> Gen Name
name mfix = do
  liftM3 Name mod (return mfix) $ case mfix of
    Nothing -> op 1
    Just _  -> op 6
  where
  character = elements "abcd"
  mod       = list' (choose (0, 2)) $ list' (choose (0, 2)) character
  op n      = list' (choose (1, n)) $ list' (choose (1, 3)) character

  list' :: Gen Integer -> Gen a -> Gen [a]
  list' = list

-- | Generates an operator.

operator :: Gen Name
operator = name . Just =<< arbitrary

prop_operator =
  forAll operator $ \op ->
    isOperator op

instance Arbitrary Name where
  arbitrary = name =<< arbitrary

  shrink (Name u f op) =
    filter nameInvariant $
    map (\(x, y, z) -> Name x y z) $
    shrink (u, f, op)

------------------------------------------------------------------------
-- Tests

-- | All tests.

tests = do
  quickCheck nameInvariant
  quickCheck (all nameInvariant . shrink)
  quickCheck prop_ignoreAssoc
  quickCheck prop_operator
