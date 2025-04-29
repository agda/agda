module QualifiedPatternInMutualBlock where

module M where
  data Unit : Set where
    tt : Unit

tt : M.Unit

f : M.Unit → M.Unit
f M.tt = tt

_*_ : M.Unit → M.Unit → M.Unit
M.tt * x = x

tt = M.tt

-- WAS: error: [Syntax.AmbiguousFunClauses]
-- More than one matching type signature for left hand side
