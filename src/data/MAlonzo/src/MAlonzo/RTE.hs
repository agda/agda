module MAlonzo.RTE where

import Unsafe.Coerce

-- Special version of coerce that plays well with rules.
{-# INLINE [1] coe #-}
coe = Unsafe.Coerce.unsafeCoerce
{-# RULES "coerce-id" forall (x :: a) . coe x = x #-}

-- Builtin QNames, the third field is for the type.
data QName a b = QName { nameId, moduleId :: Integer, qnameType :: a, qnameDefinition :: b, qnameString :: String}

instance Eq (QName a b) where
  QName a b _ _ _ == QName c d _ _ _ = (a, b) == (c, d)

instance Ord (QName a b) where
  compare (QName a b _ _ _) (QName c d _ _ _) = compare (a, b) (c, d)

mazIncompleteMatch :: String -> a
mazIncompleteMatch s = error ("MAlonzo Runtime Error: incomplete pattern matching: " ++ s)

mazUnreachableError :: a
mazUnreachableError = error ("MAlonzo Runtime Error: unreachable code reached.")

