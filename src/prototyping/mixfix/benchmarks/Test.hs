------------------------------------------------------------------------
-- Tests the precedence handling using several different parser
-- backends
------------------------------------------------------------------------

{-# LANGUAGE ExistentialQuantification, Rank2Types #-}

-- Summary: The trie parsers (which do left factorisation on the fly)
-- all seem to be reasonably efficient. The memoised backtracking and
-- CPS parsers are even faster (possibly asymptotically more
-- efficient); on the other hand they make the code constructing the
-- parser a bit more complicated. However, an important point in
-- favour of MemoisedCPS is that it supports left recursion. ReadP and
-- incremental-parser are too slow for these grammars. Note that
-- applying one of the continuation transformers to, say, AmbExTrie2
-- makes it a lot slower (in this context, anyway).
--
-- Note that if the best parsers used here are not fast enough, then
-- we can apply another optimisation: pruning the graph, keeping only
-- those nodes which have operator parts occurring in the expression
-- at hand. I think that this covers all practical cases. If someone
-- actually tries to make things hard for the parser, then it might
-- not, though.
--
-- One can guarantee polynomial complexity of parsing (for
-- context-free grammars) by, among other things, using a dense
-- representation of ambiguous results. However, the most ambiguous
-- result in the test below has length 2, and I think that we won't
-- encounter very much more than that in practice.

module Main where

import qualified ReadPWrapper as ReadP
import qualified AmbTrie
import qualified AmbExTrie
import qualified AmbExTrie2
import qualified ContTrans
import qualified StackContTrans
import qualified SlowParser
import qualified Standard
import qualified Memoised
import qualified Incremental
import qualified MemoisedCPS
import Control.Monad.Identity
import Control.Monad.State hiding (lift)
import Parser (Parser)
import System.Environment
import PrecedenceGraph hiding (tests)
import Data.Char
import qualified Data.List as List

------------------------------------------------------------------------
-- Encapsulating parser libraries

data P k r' tok = forall p. Parser p k r' tok =>
                  P (forall r. p r -> [tok] -> [r])

parse :: P k r' tok -> (forall p. Parser p k r' tok => p r) ->
         [tok] -> [r]
parse (P p) g = p g

parser :: Ord tok => Integer -> P k r' tok
parser  0 = P ReadP.parse
parser  1 = P AmbTrie.parse
parser  2 = P AmbExTrie.parse
parser  3 = P AmbExTrie2.parse
parser  4 = P (ContTrans.parse AmbExTrie2.parse)
parser  5 = P (StackContTrans.parse AmbExTrie2.parse)
parser  6 = P SlowParser.parse
parser  7 = P Standard.parse
parser  8 = P Memoised.parse
parser  9 = P (ContTrans.parse Memoised.parse)
parser 10 = P (StackContTrans.parse Memoised.parse)
parser 11 = P Incremental.parse
parser 12 = P MemoisedCPS.parse
parser  _ = error "No more parser combinator libraries."

------------------------------------------------------------------------
-- Test driver

test :: P Node Expr Token -> PrecedenceGraph ->
        String -> [Expr] -> IO ()
test p g s es =
  putStrLn $ pad 40 (show s) ++ pad 8 (isOK ++ ": ")
                             ++ pad 90 (show es')
  where
  pad n s = take n s ++ replicate (n - length s) ' ' ++ " "

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
lift f = StateT (Identity . f)

lift0 :: (s -> s) -> State s ()
lift0 f = StateT (\x -> Identity ((), f x))

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
-- A demanding graph

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
  test' "x [[ x ]] [[ x ]]"                    [Op "_[[_]]" [Op "_[[_]]" [a, a], a]]
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

  test' (nested nestingDepth)                  [nestedResult nestingDepth]
  test' (assoc  nestingDepth)                  [assocResult  nestingDepth]

  test'' 6 2 6
  test'' 6 1 5
  test'' 10 1 8
  test'' 12 2 11
  test'' 17 1 17
  where
  a      = AtomE
  test_n = test (parser n)

  test'    = test_n example

  nestingDepth = 100

  iterateN n f x = List.iterate f x List.!! n

  nested       d = iterateN d (\s -> "x [[ " ++ s ++ " ]]") "x"
  nestedResult d = iterateN d (\x -> Op "_[[_]]" [a, x]) a

  assoc       d = iterateN d ("x + " ++) "x"
  assocResult d = iterateN d (\x -> Op "_+_" [x, a]) a

  -- Precondition: m >= j > i > 0.
  test'' m i j = test_n (snd $ stressTest m)
                        (unwords ["x", op 'a' i, "x", op 'b' j, "x"])
                        [Op (op' 'a' i) [a, Op (op' 'b' j) [a, a]]]
    where
    op  c i = c : show i
    op' c i = "_" ++ op c i ++ "_"
