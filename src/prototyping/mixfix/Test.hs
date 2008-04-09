------------------------------------------------------------------------
-- Tests the precedence handling using several different parser
-- backends
------------------------------------------------------------------------

-- Summary: The trie parsers (which do left factorisation on the fly)
-- all seem to be reasonably efficient. There are faster
-- parsers/parser combinators, but they may be unnecessary, unless
-- someone decides to define and use horribly ambiguous operators.
-- ReadP is too slow for these grammars. Note that applying one of the
-- continuation transformers to, say, AmbExTrie2 makes it a lot slower
-- (in this context, anyway).

{-# LANGUAGE ExistentialQuantification, Rank2Types,
             MultiParamTypeClasses, FlexibleInstances,
             FlexibleContexts #-}

module Main where

import qualified ReadP
import qualified AmbTrie
import qualified AmbExTrie
import qualified AmbExTrie2
import qualified ContTrans
import qualified StackContTrans
import qualified SlowParser
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
parser 4 = P (ContTrans.parse AmbExTrie2.parse)
parser 5 = P (StackContTrans.parse AmbExTrie2.parse)
parser 6 = P SlowParser.parse
parser _ = error "No more parser combinator libraries."

------------------------------------------------------------------------
-- Test driver

test :: P Token -> PrecedenceGraph -> String -> [Expr] -> IO ()
test p g s es =
  putStrLn $ pad 40 (show s) ++ pad 8 (isOK ++ ": ") ++ show es'
  where
  pad n s = s ++ replicate (n - length s) ' '

  es'  = parse p (expressionParser g) (lex s)

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

lift0 :: (s -> s) -> State s ()
lift0 f = State (\x -> ((), f x))

unrelated'    op fix     = lift  $ unrelated    op fix
bindsAs'      op fix n   = lift0 $ bindsAs      op fix n
bindsBetween' op fix t l = lift  $ bindsBetween op fix t l

-- Note that this graph is not intended to be representative of how I
-- want operator precedences to be specified for the operators given.

example :: PrecedenceGraph
example = flip execState empty $ do
  eq   <- unrelated'    ["="]                  (Infix Non)
  unrelated'            ["<",">"]              (Infix Non)
  plus <- bindsBetween' ["+"]                  (Infix L)   [eq]   []
  bindsAs'              ["-"]                  (Infix R)   plus
  mul  <- bindsBetween' ["*"]                  (Infix L)   [plus] []
  bindsAs'              ["/"]                  (Infix L)   mul
  pow  <- bindsBetween' ["^"]                  (Infix R)   [mul]  []
  or   <- bindsBetween' ["||"]                 (Infix R)   [eq]   []
  not  <- bindsBetween' ["!"]                  Prefix      [or]   []
  and  <- bindsBetween' ["&&"]                 (Infix R)   [or]   [not, plus]
  eq'  <- bindsBetween' ["=="]                 (Infix Non) []     [or]
  ite  <- bindsBetween' ["if", "then", "else"] Prefix      [eq]   [and, mul]
  bindsAs'              ["if", "then"]         Prefix      ite
  ox   <- unrelated'    ["[[","]]"]            Postfix
  bindsAs'              ["[[","]]*"]           Postfix     ox
  bindsAs'              ["[[","]]+"]           Prefix      ox
  unrelated'            ["foo"]                (Infix L)
  unrelated'            ["foo"]                (Infix R)
  unrelated'            ["<<",">>"]            (Infix L)
  unrelated'            [">>","<<"]            (Infix Non)

------------------------------------------------------------------------
-- A very ambiguous graph

-- stressTest n yields a graph which is the transitive closure of a
-- graph with the following shape (with edges going upwards):
--
--  ⋱  ⋮  ⋰
--   ⋱ ⋮ ⋰
--    ⋱⋮⋰
--     n₂
--    ╱│╲
--   ╱ │ ╲
--  ╱  │  ╲
-- a₂  b₂  c₂
--  ╲  │  ╱
--   ╲ │ ╱
--    ╲│╱
--     n₁
--    ╱│╲
--   ╱ │ ╲
--  ╱  │  ╲
-- a₁  b₁  c₁
--  ╲  │  ╱
--   ╲ │ ╱
--    ╲│╱
--     n₀
--
-- The top-most node is n_n.

-- These graphs are tricky to parse for all but small n, or if the
-- "width" is increased too much. If this should turn out to be a
-- problem in practice we have (at least) two ways out:
--
-- ⑴ Prune the graph, keeping only those nodes which have operator
--   parts occurring in the expression at hand. I think that this
--   covers all practical cases. If someone actually tries to make
--   things hard for the parser, then it won't, though.
--
-- ⑵ Use a more efficient parser backend.

stressTest :: Integer -> (Node, PrecedenceGraph)
stressTest n | n <= 0 = unrelated ["n0"] (Infix Non) empty
stressTest n = flip runState g $ do
  cs <- mapM (\c -> bindsBetween' (name c) (Infix Non) [node] [])
             ['a'..'c']
  bindsBetween' (name 'n') (Infix Non) cs []
  where
  (node, g) = stressTest (n - 1)
  name c    = [c : show n]

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
  test' "x + y - z"                            []
  test' "x * y / z"                            [Op "_/_" [Op "_*_" [a, a], a]]
  test' "x + y && z"                           [Op "_&&_" [Op "_+_" [a, a], a]]
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

  test'' 6 2 6
  test'' 6 1 5
  test'' 10 1 8
  test'' 12 2 11
  where
  a      = AtomE
  test_n = test (parser n)

  test'  = test_n example

  -- Precondition: m >= j > i > 0.
  test'' m i j = test_n (snd $ stressTest m)
                        (unwords ["x", op 'a' i, "x", op 'b' j, "x"])
                        [Op (op' 'a' i) [a, Op (op' 'b' j) [a, a]]]
    where
    op  c i = c : show i
    op' c i = "_" ++ op c i ++ "_"
