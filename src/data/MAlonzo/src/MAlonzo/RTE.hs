module MAlonzo.RTE where

import Unsafe.Coerce
import GHC.Prim

-- Special version of coerce that plays well with rules.
{-# INLINE [1] coe #-}
coe = unsafeCoerce
{-# RULES "coerce-id" forall (x :: a) . coe x = x #-}

-- Builtin QNames, the third field is for the type.
data QName a b = QName { nameId, moduleId :: Integer, qnameType :: a, qnameDefinition :: b, qnameString :: String}

instance Eq (QName a b) where
  QName a b _ _ _ == QName c d _ _ _ = (a, b) == (c, d)

instance Ord (QName a b) where
  compare (QName a b _ _ _) (QName c d _ _ _) = compare (a, b) (c, d)

erased :: Any
erased = unsafeCoerce (\ _ -> erased)

mazIncompleteMatch :: String -> a
mazIncompleteMatch s = error ("Agda: incomplete pattern matching: " ++ s)

mazUnreachableError :: a
mazUnreachableError = error ("Agda: unreachable code reached.")

