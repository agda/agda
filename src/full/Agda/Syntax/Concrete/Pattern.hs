-- | Tools for patterns in concrete syntax.

module Agda.Syntax.Concrete.Pattern where

import Agda.Syntax.Concrete

class IsEllipsis a where
  isEllipsis :: a -> Bool

-- | Is the pattern just '...'?
instance IsEllipsis Pattern where
  isEllipsis = \case
    EllipsisP{}   -> True
    RawAppP _ [p] -> isEllipsis p
    ParenP _ p    -> isEllipsis p
    _ -> False

-- | Does the lhs contain an ellipsis?
instance IsEllipsis LHS where
  isEllipsis (LHS p _ _ _) = isEllipsis p
