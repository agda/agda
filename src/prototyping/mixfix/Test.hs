------------------------------------------------------------------------
-- Tests the precedence handling using several different parser
-- backends
------------------------------------------------------------------------

-- Summary: The trie parsers (which do left factorisation on the fly)
-- all seem to be reasonably efficient. There are faster
-- parsers/parser combinators, but they may be unnecessary, unless
-- someone decides to define and use horribly ambiguous operators.
-- ReadP is a bit too slow for these grammars (∼ 10 times slower on
-- the tests below), perhaps because the grammars are slightly
-- ambiguous.

{-# LANGUAGE ExistentialQuantification, Rank2Types,
             MultiParamTypeClasses, FlexibleInstances,
             FlexibleContexts #-}

module Main where

import qualified ReadP
import qualified AmbTrie
import qualified AmbExTrie
import qualified AmbExTrie2
import Control.Monad
import Control.Monad.State hiding (lift)
import qualified Parser
import Parser (Parser)
import System.Environment
import PrecedenceGraph
import Data.Char
import qualified Data.List as List
import qualified Control.Applicative as A

------------------------------------------------------------------------
-- Encapsulating parser libraries

instance A.Applicative (ReadP.ReadP tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> p2 >>= \x -> return (f x)

instance A.Alternative (ReadP.ReadP tok) where
  empty = mzero
  (<|>) = mplus

instance Ord tok => Parser (ReadP.ReadP tok) tok where
  sym       = ReadP.char
  parse     = ReadP.parse

  choice    = ReadP.choice
  many1     = ReadP.many1
  chainr1   = ReadP.chainr1
  chainl1   = ReadP.chainl1

data P tok = forall p. Parser p tok =>
             P (forall r. p r -> [tok] -> [r])

parse :: Ord tok =>
         P tok -> (forall p. Parser p tok => p r) -> [tok] -> [r]
parse (P p) g = p g

parser :: Ord tok => Integer -> P tok
parser 0 = P ReadP.parse
parser 1 = P AmbTrie.parse
parser 2 = P AmbExTrie.parse
parser 3 = P AmbExTrie2.parse
parser _ = error "No more parser combinator libraries."

------------------------------------------------------------------------
-- Test driver

test :: Bool -> P Token -> String -> [Expr] -> IO ()
test remDups p s es =
  putStrLn $ pad 40 (show s) ++ pad 8 (isOK ++ ": ") ++ show es'
  where
  pad n s = s ++ replicate (n - length s) ' '

  es'  = parse p (expressionParser example) (lex s)

  isOK | List.sort es' == List.sort es = "OK"
       | otherwise                     = "Not OK"

  lex = map toToken . words
    where
    toToken [c] | isAlpha c = Atom
    toToken cs              = Name cs

main = do
  [which] <- fmap (map read) getArgs
  tests which

------------------------------------------------------------------------
-- Example precedence graph

lift :: (s -> (a, s)) -> State s a
lift = State

lift0 :: (s -> s) -> State s s
lift0 f = State (\x -> let s' = f x in (s', s'))

unrelated'    op fix     = lift  $ unrelated    op fix        
bindsAs'      op fix n   = lift0 $ bindsAs      op fix n       
bindsBetween' op fix t l = lift  $ bindsBetween op fix t l 

example :: PrecedenceGraph
example = flip execState empty $ do
  eq   <- unrelated'    ["="]                  (Infix Non)
  unrelated'            ["<",">"]              (Infix Non)
  plus <- bindsBetween' ["+"]                  (Infix L)   [eq]   []
  bindsAs'              ["-"]                  (Infix L)   plus
  mul  <- bindsBetween' ["*"]                  (Infix L)   [plus] []
  bindsAs'              ["/"]                  (Infix L)   mul
  pow  <- bindsBetween' ["^"]                  (Infix R)   [mul]  []
  or   <- bindsBetween' ["||"]                 (Infix R)   [eq]   []
  not  <- bindsBetween' ["!"]                  Prefix      [or]   []
  and  <- bindsBetween' ["&&"]                 (Infix R)   [or]   [not]
  eq'  <- bindsBetween' ["=="]                 (Infix Non) []     [or]
  ite  <- bindsBetween' ["if", "then", "else"] Prefix      [eq]   []
  bindsAs'              ["if", "then"]         Prefix      ite
  ox   <- unrelated'    ["[[","]]"]            Postfix
  bindsAs'              ["[[","]]*"]           Postfix     ox
  bindsAs'              ["[[","]]+"]           Prefix      ox
  unrelated'            ["foo"]                (Infix L)
  unrelated'            ["foo"]                (Infix R)
  unrelated'            ["<<",">>"]            (Infix L)
  unrelated'            [">>","<<"]            (Infix Non)

------------------------------------------------------------------------
-- Tests

tests n = do
  test' "x"                                    [a]
  test' "x = x"                                [Op "_=_" [a, a]]
  test' "x = x = x"                            []
  test' "x < x > x"                            [Op "_<_>_" [a, a, a]]
  test' "x < x = x > x"                        [Op "_<_>_" [a, Op "_=_" [a, a], a]]
  test' "x + x"                                [Op "_+_" [a, a]]
  test' "x + y + z"                            [Op "_+_" [Op "_+_" [a, a], a]]
  test' "x + y - z"                            [Op "_-_" [Op "_+_" [a, a], a]]
  test' "x + y && z"                           []
  test' "x ^ y ^ z"                            [Op "_^_" [a, Op "_^_" [a, a]]]
  test' "! x"                                  [Op "!_" [a]]
  test' "! ! x"                                [Op "!_" [Op "!_" [a]]]
  test' "! x + y"                              []
  test' "! x && y"                             [Op "_&&_" [Op "!_" [a], a]]
  test' "x [[ x [[ x ]]* ]]"                   [Op "_[[_]]" [a, Op "_[[_]]*" [a, a]]]
  test' "x [[ x ]] [[ x ]]*"                   [Op "_[[_]]*" [Op "_[[_]]" [a, a], a]]
  test' "x << x >> x << x >> x"                [ Op "_<<_>>_" [a, Op "_>>_<<_" [a, a, a], a]
                                               , Op "_<<_>>_" [Op "_<<_>>_" [a, a, a], a, a] ]
  test' "if x then a else b"                   [Op "if_then_else_" [a, a, a]]
  test' "if x then if y then a else b else c"  [Op "if_then_else_" [a, Op "if_then_else_" [a, a, a], a]]
  test' "if x then if y then a else b"         [ Op "if_then_else_" [a, Op "if_then_" [a, a], a]
                                               , Op "if_then_" [a, Op "if_then_else_" [a, a, a]] ]
  test' "if x then a + b else c = d"           [Op "_=_" [Op "if_then_else_" [a, Op "_+_" [a, a], a], a]]
  test' "x foo x foo x"                        [ Op "_foo_" [a, Op "_foo_" [a, a]]
                                               , Op "_foo_" [Op "_foo_" [a, a], a] ]
  test' "x foo x foo x foo x"                  [ Op "_foo_" [a, Op "_foo_" [a, Op "_foo_" [a, a]]]
                                               , Op "_foo_" [Op "_foo_" [Op "_foo_" [a, a], a], a] ]
  where
  a     = AtomE
  test' = test True (parser n)
