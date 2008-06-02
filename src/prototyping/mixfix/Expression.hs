------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

module Expression where

import Name hiding (tests)

import Test.QuickCheck
import Control.Monad
import Data.List

-- | Expressions.

data Expr = Fun Name
          | App Expr Expr
          | Op Name [Maybe Expr]
            -- ^ An application of an operator to /all/ its arguments.
            -- 'Nothing' stands for a placeholder.
          | WildcardE
  deriving (Eq, Ord, Show)

-- | The expression invariant.

exprInvariant :: Expr -> Bool
exprInvariant (Fun n)     = nameInvariant n
exprInvariant (App e1 e2) = exprInvariant e1 && exprInvariant e2
exprInvariant (Op op es)  = isOperator op &&
                            genericLength es == arity op &&
                            nameInvariant op &&
                            all (maybe True exprInvariant) es
exprInvariant WildcardE   = True

-- | Application of something to multiple arguments (possibly zero).

app :: Expr -> [Expr] -> Expr
app e args = foldl App e args

------------------------------------------------------------------------
-- Test data generators

instance Arbitrary Expr where
  arbitrary = sized expr
    where
    expr n | n <= 0 = oneof [ liftM Fun arbitrary
                            , return WildcardE
                            ]
    expr n = frequency [ (2, expr 0)
                       , (1, liftM2 App (e 2) (e 2))
                       , (1, do
                            op <- operator
                            let a = fromInteger $ arity op
                            es <- vectorOf a (oneof [ return Nothing
                                                    , liftM Just (e a)
                                                    ])
                            return (Op op es))
                       ]
      where e d = expr (n `div` d)

------------------------------------------------------------------------
-- Tests.

-- | All tests.

tests = do
  quickCheck exprInvariant
