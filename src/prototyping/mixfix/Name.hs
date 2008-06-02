------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

module Name
  ( Assoc(..)
  , Fixity(..)
  , fixAssocInvariant
  , ignoreAssoc
  , Name(..)
  , arity
  , isOperator
  , isOpenOperator
  , nameInvariant
  , pretty
  , string
  , name
  , operator
  , openOperator
  , tests
  ) where

import Data.Function
import qualified Data.Maybe as Maybe
import Control.Monad
import Test.QuickCheck
import qualified Data.List as List

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

-- | The arity of an operator (zero for non-operators).

arity :: Name -> Integer
arity n = List.genericLength (nameParts n) + case fixity n of
  Nothing      -> - 1
  Just Prefix  -> 0
  Just Postfix -> 0
  Just Infix   -> 1

-- | Is the name an operator?

isOperator :: Name -> Bool
isOperator = (> 0) . arity

-- | Is the name an open operator?

isOpenOperator :: Name -> Bool
isOpenOperator = Maybe.isJust . fixity

-- | The name invariant.

nameInvariant n@(Name m f ns) = nonEmpty ns && all nonEmpty ns
  where nonEmpty = not . null

-- | Pretty-prints a name.

pretty :: Name -> String
pretty n = List.intercalate "." (moduleName n ++ [name])
  where
  fixUp = case fixity n of
    Nothing      -> id
    Just Prefix  -> (++ "_")
    Just Postfix -> ("_" ++)
    Just Infix   -> ("_" ++) . (++ "_")
  name = fixUp (List.intercalate "_" $ nameParts n)

------------------------------------------------------------------------
-- Test data generators

instance Arbitrary Assoc where
  arbitrary = elements [Non, L, R]

instance Arbitrary Fixity where
  arbitrary = elements [Prefix, Postfix, Infix]

-- | Generates a string, of the given minimum and maximum lengths,
-- suitable for use in a name.

string :: Integer -- ^ Minimum length.
       -> Integer -- ^ Maximum length.
       -> Gen String
string min max = list (choose (min, max)) (elements "ab")

-- | Generates a name with the given fixity.

name :: Maybe Fixity -> Gen Name
name mfix = liftM3 Name mod (return mfix) op
  where
  character = elements "abcd"
  mod       = list (choose (0, 2 :: Integer)) $ string 1 1
  op        = list (choose (1, 3 :: Integer)) $ string 1 2

-- | Generates an open operator.

openOperator :: Gen Name
openOperator = name . Just =<< arbitrary

prop_openOperator =
  forAll openOperator $ \op ->
    isOpenOperator op

-- | Generates an operator.

operator :: Gen Name
operator = arbitrary `suchThat` isOperator

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
  quickCheck prop_openOperator
