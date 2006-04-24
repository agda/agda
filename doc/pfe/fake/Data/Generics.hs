module Data.Generics where
-- | Parts of the ghc library Generics.hs

-- | Fixity of constructors
data Fixity = Prefix
            | Infix	-- Later: add associativity and precedence

	    deriving (Eq,Show)

class Typeable a where
  typeOf :: a -> TypeRep

class Typeable a => Data a where


data TypeRep = Dummy

dummy_declaration = True

newtype GenericT'   = GT { unGT :: a -> a }
