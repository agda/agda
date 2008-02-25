
module TypeChecking.Injectivity where

import Control.Applicative

import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute

checkInjectivity :: [Clause] -> TCM FunctionInverse
checkInjectivity _ = return NotInjective

functionInverse :: QName -> TCM FunctionInverse
functionInverse f = do
  d <- theDef <$> getConstInfo f
  case d of
    Function _ inv _ -> return inv
    _                -> return NotInjective

useInjectivity :: Type -> Term -> Term -> TCM Constraints
useInjectivity a u v = buildConstraint $ ValueEq a u v

tryInverse :: Type -> QName -> Args -> Term -> TCM Constraints
tryInverse a f us v = do
  inv <- functionInverse f
  case inv of
    NotInjective -> fallBack
    Inverse inv  -> do
      fallBack
  where
    fallBack = buildConstraint $ ValueEq a (Def f us) v

