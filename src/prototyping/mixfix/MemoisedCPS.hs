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

-- Another change has also been made: the user does not have to insert
-- memoisation annotations manually. Instead all grammar non-terminals
-- are memoised.

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}

module MemoisedCPS (Parser, parse) where

import Control.Applicative
import Control.Monad.State.Lazy
import Data.Array
import Data.List
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import qualified IndexedMap as IMap
import IndexedOrd
import qualified Parser

-- | Positions.

type Pos = Int

-- | State monad used by the parser.

type M nt tok b = State (IntMap (IMap.Map nt (Value nt tok b)))

-- | Continuations.

type Cont nt tok b a = Pos -> a -> M nt tok b [b]

-- | Memoised values.

data Value nt tok b a = Value
  { results       :: IntMap [a]
  , continuations :: [Cont nt tok b a]
  }

-- | The parser type.

newtype Parser nt tok a =
  P { unP :: forall b.
             Parser.Grammar (Parser nt tok) nt ->
             Array Pos tok ->
             Pos ->
             Cont nt tok b a ->
             M nt tok b [b]
    }

instance Monad (Parser nt tok) where
  return x  = P $ \_ _ i k -> k i x
  P p >>= f = P $ \g input i k ->
    p g input i $ \j x -> unP (f x) g input j k

instance Functor (Parser nt tok) where
  fmap f p = p >>= return . f

instance Applicative (Parser nt tok) where
  pure  = return
  (<*>) = ap

instance Alternative (Parser nt tok) where
  empty         = P $ \_ _ _ _ -> return []
  P p1 <|> P p2 = P $ \g input i k ->
    liftM2 (++) (p1 g input i k) (p2 g input i k)

-- | Runs the parser.

parse :: Parser.Grammar (Parser nt tok) nt ->
         Parser nt tok r -> [tok] -> [r]
parse g p toks =
  flip evalState IntMap.empty $
  unP p g (listArray (0, n - 1) toks) 0 $ \j x ->
    if j == n then return [x] else return []
  where n = genericLength toks

instance Parser.Parser (Parser nt tok) tok where
  symbol = P $ \_ input i k ->
    if inRange (bounds input) i then
      k (i + 1) (input ! i)
     else
      return []

  parse = parse (const empty)

-- | Non-terminals are memoised.

instance Parser.NTParser (Parser nt tok) nt tok where
  nonTerm nt = P $ \grammar input i k -> do

    let alter j zero f m =
          IntMap.alter (Just . f . maybe zero id) j m

        lookupTable   = fmap (\m -> IMap.lookup nt =<<
                                    IntMap.lookup i m) get
        insertTable v = modify $ alter i IMap.empty (IMap.insert nt v)

    v <- lookupTable
    case v of
      Nothing -> do
        insertTable (Value IntMap.empty [k])
        unP (grammar nt) grammar input i $ \j r -> do
          Just (Value rs ks) <- lookupTable
          insertTable (Value (alter j [] (r :) rs) ks)
          concat <$> mapM (\k -> k j r) ks  -- See note [Reverse ks?].
      Just (Value rs ks) -> do
        insertTable (Value rs (k : ks))
        concat . concat <$>
          mapM (\(i, rs) -> mapM (k i) rs) (IntMap.toList rs)

  parseWithGrammar = parse

-- [Reverse ks?]
--
-- If ks were reversed, then the code would be productive for some
-- infinitely ambiguous grammars, including S ∷= S | ε. However, in
-- some cases the results would not be fair (some valid results would
-- never be returned).
