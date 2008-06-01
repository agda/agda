------------------------------------------------------------------------
-- Expressions and tokens
------------------------------------------------------------------------

module Expression where

import Name

-- | Expressions.

data Expr = Fun Name
          | App Expr [Expr]
            -- ^ Note that the application of an operator to its
            -- arguments is represented using 'Op', not 'App'.
          | Op Name [Maybe Expr]
            -- ^ An application of an operator to /all/ its arguments.
            -- 'Nothing' stands for a placeholder.
          | WildcardE
  deriving (Eq, Ord, Show)

-- | Tokens. Placeholders are used to indicate sections. Wildcards
-- indicate things the type checker should fill in automatically
-- (hopefully). Name parts stand for operator name parts (and possibly
-- other identifiers as well).

data Token = NamePart String | Placeholder Pos
           | Wildcard | LParen | RParen
  deriving (Eq, Ord, Show)

-- | Placeholder positions.

data Pos = Beg  -- ^ At the beginning of an operator.
         | Mid  -- ^ In the middle of an operator.
         | End  -- ^ At the end of an operator.
  deriving (Eq, Ord, Show)
