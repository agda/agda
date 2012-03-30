------------------------------------------------------------------------
-- Parser combinators with support for left recursion, following
-- Johnson's "Memoization in Top-Down Parsing"
------------------------------------------------------------------------

-- This implementation is based on an implementation due to Atkey
-- (attached to an edlambda-members mailing list message from
-- 2011-02-15 titled 'Slides for "Introduction to Parser
-- Combinators"').

-- Note that non-memoised left recursion is not guaranteed to work.

-- The code contains an important deviation from Johnson's paper: the
-- check for subsumed results is not included. This means that one can
-- get the same result multiple times when parsing using ambiguous
-- grammars. As an example, parsing the empty string using S ∷= ε | ε
-- succeeds twice. This change also means that parsing fails to
-- terminate for some cyclic grammars that would otherwise be handled
-- successfully, such as S ∷= S | ε. However, the library is not
-- intended to handle infinitely ambiguous grammars. (It is unclear to
-- me whether the change leads to more non-termination for grammars
-- which are not cyclic.)

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}

module MemoisedCPS (Parser, parse) where

import Control.Applicative
import Control.Monad.State.Lazy
import Data.Array
import Data.List
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import qualified Data.Map as Map
import Data.Map (Map)

import qualified Parser

-- | Positions.

type Pos = Int

-- | State monad used by the parser.

type M k r tok b = State (IntMap (Map k (Value k r tok b)))

-- | Continuations.

type Cont k r tok b a = Pos -> a -> M k r tok b [b]

-- | Memoised values.

data Value k r tok b = Value
  { results       :: IntMap [r]
  , continuations :: [Cont k r tok b r]
  }

-- | The parser type.

newtype Parser k r tok a =
  P { unP :: forall b.
             Array Pos tok ->
             Pos ->
             Cont k r tok b a ->
             M k r tok b [b]
    }

instance Monad (Parser k r tok) where
  return x  = P $ \_ i k -> k i x
  P p >>= f = P $ \input i k ->
    p input i $ \j x -> unP (f x) input j k

instance Functor (Parser k r tok) where
  fmap f p = p >>= return . f

instance Applicative (Parser k r tok) where
  pure  = return
  (<*>) = ap

instance Alternative (Parser k r tok) where
  empty         = P $ \_ _ _ -> return []
  P p1 <|> P p2 = P $ \input i k ->
    liftM2 (++) (p1 input i k) (p2 input i k)

-- | Runs the parser.

parse :: Parser k r tok a -> [tok] -> [a]
parse p toks =
  flip evalState IntMap.empty $
  unP p (listArray (0, n - 1) toks) 0 $ \j x ->
    if j == n then return [x] else return []
  where n = genericLength toks

instance Parser.Parser (Parser k r tok) k r tok where
  sym c = P $ \input i k ->
    let c' = input ! i in
    if inRange (bounds input) i && c == c' then
      k (i + 1) c'
     else
      return []

  memoise key p = P $ \input i k -> do

    let alter j zero f m =
          IntMap.alter (Just . f . maybe zero id) j m

        lookupTable   = fmap (\m -> Map.lookup key =<<
                                    IntMap.lookup i m) get
        insertTable v = modify $ alter i Map.empty (Map.insert key v)

    v <- lookupTable
    case v of
      Nothing -> do
        insertTable (Value IntMap.empty [k])
        unP p input i $ \j r -> do
          Just (Value rs ks) <- lookupTable
          insertTable (Value (alter j [] (r :) rs) ks)
          concat <$> mapM (\k -> k j r) ks  -- See note [Reverse ks?].
      Just (Value rs ks) -> do
        insertTable (Value rs (k : ks))
        concat . concat <$>
          mapM (\(i, rs) -> mapM (k i) rs) (IntMap.toList rs)

-- [Reverse ks?]
--
-- If ks were reversed, then the code would be productive for some
-- infinitely ambiguous grammars, including S ∷= S | ε. However, in
-- some cases the results would not be fair (some valid results would
-- never be returned).
