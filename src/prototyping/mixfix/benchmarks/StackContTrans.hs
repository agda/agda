------------------------------------------------------------------------
-- Another continuation transformer (see Ljunglöf's licentiate thesis)
------------------------------------------------------------------------

{-# LANGUAGE Rank2Types, MultiParamTypeClasses, FlexibleInstances,
             UndecidableInstances #-}

module StackContTrans where

import Control.Applicative
import Control.Monad
import qualified Parser

newtype StackContTrans p r =
  P { unP :: forall r' r''. (r' -> p r'') -> (r -> r') -> p r'' }

instance Functor (StackContTrans p) where
  fmap f (P p) = P (\k s -> p k (s . f))

instance Applicative (StackContTrans p) where
  pure x        = P (\k s -> k (s x))
  P p1 <*> P p2 = P (\k s -> p1 (p2 k) (\f x -> s (f x)))

instance Alternative p => Alternative (StackContTrans p) where
  empty         = P (\_ _ -> empty)
  P p1 <|> P p2 = P (\k s -> p1 k s <|> p2 k s)

parse :: Applicative p =>
         (p r -> [tok] -> [r]) ->
         (StackContTrans p r -> [tok] -> [r])
parse parse' (P p) = parse' (p pure id)

instance (Ord tok, Alternative p, Monad p, Parser.Parser p k r' tok) =>
         Parser.Parser (StackContTrans p) k r' tok where
  sym c = P (\k s -> Parser.sym c >>= k . s)
