
module Types.Monad
  ( module Types.Monad
  , module IMPL.Monad
  ) where

import Control.Applicative
import Data.Traversable

import Types.Abs
import Types.Tel
import Types.Blocked
import IMPL.Monad
import IMPL.Term
import IMPL.Eval

whnfView :: Term -> TC (Blocked TermView)
whnfView v = traverse view =<< whnf v

telView :: Term -> TC (Telescope, Term)
telView a = do
  a <- whnfView a
  case a of
    NotBlocked (Pi a b) -> do
      (tel, c) <- underAbstraction a b $ \_ -> telView
      return (a :> (tel <$ b), c)
    _ -> (,) EmptyTel <$> unview (ignoreBlocking a)

extendContextTel :: Telescope -> TC a -> TC a
extendContextTel EmptyTel   ret = ret
extendContextTel (a :> tel) ret =
  underAbstraction a tel $ \_ tel ->
  extendContextTel tel ret

data ProblemId a = TODO

data Stuck a = NotStuck a | Stuck (ProblemId a)

subProblem_ :: ProblemId a -> (a -> TC b) -> TC (ProblemId b)
subProblem_ pid f = subProblem pid (\x -> NotStuck <$> f x)

subProblem :: ProblemId a -> (a -> TC (Stuck b)) -> TC (ProblemId b)
subProblem = error "subProblem"

newProblem :: MetaVar -> TC (Stuck a) -> TC (ProblemId a)
newProblem = error "newProblem"

whenStuck :: TC (Stuck a) -> (ProblemId a -> TC a) -> TC a
whenStuck m h = do
  r <- m
  case r of
    NotStuck x -> return x
    Stuck pid  -> h pid

whenStuck_ :: TC (Stuck a) -> TC a -> TC a
whenStuck_ m h = whenStuck m (const h)
