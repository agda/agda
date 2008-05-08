------------------------------------------------------------------------
-- Tests the performance and correctness of the precedence handling
------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

-- Summary: The memoising backtracking parser seems to be fast enough.
--
-- Note that if this code is not fast enough, then we can apply
-- another optimisation: pruning the graph, keeping only those nodes
-- which have operator parts occurring in the expression at hand. I
-- think that this covers all practical cases. If someone actually
-- tries to make things hard for the parser, then it might not,
-- though.
--
-- One can guarantee polynomial complexity of parsing by using a dense
-- representation of ambiguous results. However, the most ambiguous
-- result in the test below has length 2, and I think that we won't
-- encounter very much more than that in practice.

module Main where

import qualified Memoised
import Control.Monad.State hiding (lift)
import PrecedenceGraph
import ExpressionParser
import Data.Char
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Function
import Parser
import qualified Control.Applicative as A
import Prelude hiding (lex)

------------------------------------------------------------------------
-- Test driver

test :: Set Name -> PrecedenceGraph -> String -> [Expr] -> IO Bool
test closed g s es = do
  putStrLn $ pad 40 (show s) ++ pad 8 (isOK ++ ": ")
                             ++ pad 90 (show es')
  return correct
  where
  pad n s = take n s ++ replicate (n - length s) ' ' ++ " "

  es' = Memoised.parse (grammar g ident closed) (expression g) (lex s)

  correct = sort es' == sort es

  isOK = if correct then "OK" else "Not OK"

main = do
  ok <- tests
  putStrLn $ if ok then "All tests passed."
                   else "Some test failed."

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
-- want operator precedences to be specified for the given operators.

example :: PrecedenceGraph
example = flip execState empty $ do
  eq   <- unrelated'    ["="]                  (Infix Non)
  unrelated'            ["<",">"]              (Infix Non)
  plus <- bindsBetween' ["+"]                  (Infix L)   [eq]   []
  bindsAs'              ["+'"]                 (Infix L)   plus
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
  ox   <- unrelated'    ["<[","]>"]            Postfix
  bindsAs'              ["<[","]>*"]           Postfix     ox
  bindsAs'              ["<[","]>+"]           Prefix      ox
  unrelated'            ["foo"]                (Infix L)
  unrelated'            ["foo"]                (Infix R)
  unrelated'            ["<<",">>"]            (Infix L)
  unrelated'            [">>","<<"]            (Infix Non)

exampleClosed :: Set Name
exampleClosed = Set.fromList [ ["[[","]]"]
                             , ["[[", "]]*"]
                             , ["[[", "]]+"]
                             ]

------------------------------------------------------------------------
-- Lexer

-- | A simple lexer. Note that @_@ is treated differently depending on
-- whether or not it is located next to a name. Note also that
-- parentheses do not need to be separated from other tokens with
-- white space.

lex :: String -> [Token]
lex = concatMap toToken .
      filter (not . all isSpace) .
      groupBy ((&&) `on` notSpaceOrParen)
  where
  notSpaceOrParen c = not (isSpace c || c `elem` "()")

  toToken "_"             = [Wildcard]
  toToken "("             = [LParen]
  toToken ")"             = [RParen]
  toToken cs              =
    fixL $ fixR $ map toT $ groupBy ((&&) `on` (/= '_')) cs
    where
    toT "_" = Placeholder Mid
    toT cs  = Name cs

    fix p (Placeholder _ : toks) = Placeholder p : toks
    fix p toks                   = toks

    fixL = fix Beg
    fixR = reverse . fix End . reverse

-- | Parser for identifiers. For simplicity single alphabetic
-- characters are taken as function names, while other character
-- sequences are taken as operator parts.

ident :: NTParser p NT Token => p String
ident = symbol >>= \s -> case s of
  Name n@[c] | isAlpha c -> A.pure n
  _                      -> A.empty

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

tests :: IO Bool
tests = fmap and $ sequence
  [ test' "x"                                   [Fun "x"]
  , test' "x = x"                               [Op "_=_" [jF "x", jF "x"]]
  , test' "x = x = x"                           []
  , test' "x < x > x"                           [Op "_<_>_" [jF "x", jF "x", jF "x"]]
  , test' "x < x = x > x"                       [Op "_<_>_" [jF "x", jOp "_=_" [jF "x", jF "x"], jF "x"]]
  , test' "x + x"                               [Op "_+_" [jF "x", jF "x"]]
  , test' "x + y + z"                           [Op "_+_" [jOp "_+_" [jF "x", jF "y"], jF "z"]]
  , test' "x + y - z"                           []
  , test' "x * y / z"                           [Op "_/_" [jOp "_*_" [jF "x", jF "y"], jF "z"]]
  , test' "x + y && z"                          [Op "_&&_" [jOp "_+_" [jF "x", jF "y"], jF "z"]]
  , test' "x ^ y ^ z"                           [Op "_^_" [jF "x", jOp "_^_" [jF "y", jF "z"]]]
  , test' "! x"                                 [Op "!_" [jF "x"]]
  , test' "! ! x"                               [Op "!_" [jOp "!_" [jF "x"]]]
  , test' "! x + y"                             []
  , test' "! x && y"                            [Op "_&&_" [jOp "!_" [jF "x"], jF "y"]]
  , test' "x <[ x <[ x ]>* ]>"                  [Op "_<[_]>" [jF "x", jOp "_<[_]>*" [jF "x", jF "x"]]]
  , test' "x <[ x ]> <[ x ]>*"                  [Op "_<[_]>*" [jOp "_<[_]>" [jF "x", jF "x"], jF "x"]]
  , test' "x << x >> x << x >> x"               [ Op "_<<_>>_" [jF "x", jOp "_>>_<<_" [jF "x", jF "x", jF "x"], jF "x"]
                                                , Op "_<<_>>_" [jOp "_<<_>>_" [jF "x", jF "x", jF "x"], jF "x", jF "x"] ]
  , test' "if x then a else b"                  [Op "if_then_else_" [jF "x", jF "a", jF "b"]]
  , test' "if x then if y then a else b else c" [Op "if_then_else_" [jF "x", jOp "if_then_else_" [jF "y", jF "a", jF "b"], jF "c"]]
  , test' "if x then if y then a else b"        [ Op "if_then_else_" [jF "x", jOp "if_then_" [jF "y", jF "a"], jF "b"]
                                                , Op "if_then_" [jF "x", jOp "if_then_else_" [jF "y", jF "a", jF "b"]] ]
  , test' "if x then a + b else c = d"          [Op "_=_" [jOp "if_then_else_" [jF "x", jOp "_+_" [jF "a", jF "b"], jF "c"], jF "d"]]
  , test' "x foo x foo x"                       [ Op "_foo_" [jF "x", jOp "_foo_" [jF "x", jF "x"]]
                                                , Op "_foo_" [jOp "_foo_" [jF "x", jF "x"], jF "x"] ]
  , test' "x foo x foo x foo x"                 [ Op "_foo_" [jF "x", jOp "_foo_" [jF "x", jOp "_foo_" [jF "x", jF "x"]]]
                                                , Op "_foo_" [jOp "_foo_" [jOp "_foo_" [jF "x", jF "x"], jF "x"], jF "x"] ]
  , test' "_"                                   [w]
  , test' "_+_"                                 [Op "_+_" [p, p]]
  , test' "_ + _"                               [Op "_+_" [Just w, Just w]]
  , test' "if_then a + _ else_ = d"             [Op "_=_" [jOp "if_then_else_" [p, jOp "_+_" [jF "a", Just w], p], jF "d"]]
  , test' "if__then a + _ else_ = d"            []
  , test' "f (_+_)"                             [App (Fun "f") [Op "_+_" [p, p]]]
  , test' "(_+_) f"                             [App (Op "_+_" [p, p]) [Fun "f"]]
  , test' "f _+_"                               [App (Fun "f") [Op "_+_" [p, p]]]
  , test' "f _ +_"                              [Op "_+_" [jApp (Fun "f") [w], p]]
  , test' "(((f))) (((x))) (((y)))"             [App (Fun "f") [Fun "x", Fun "y"]]
  , test' "(_)"                                 [w]
  , test' "_<[_]>"                              [Op "_<[_]>" [p, p]]
  , test' "_+ _+'_"                             [Op "_+_" [p, jOp "_+'_" [p, p]]]
  , test' "_+_ +'_"                             [Op "_+'_" [jOp "_+_" [p, p], p]]
  , test' "f (x <[ y ]>) + z"                   [Op "_+_" [jApp (Fun "f") [Op "_<[_]>" [jF "x", jF "y"]], jF "z"]]
  , test' "f (_+_ <[ y ]>) + z"                 [Op "_+_" [jApp (Fun "f") [Op "_<[_]>" [jOp "_+_" [p, p], jF "y"]], jF "z"]]
  , test' "f (x <[ _+_ ]>) + z"                 [Op "_+_" [jApp (Fun "f") [Op "_<[_]>" [jF "x", jOp "_+_" [p, p]]], jF "z"]]
  , test' "f x <[ _+_ ]> + z"                   []
  , test' "f x <[ _+_ ]>"                       [Op "_<[_]>" [jApp (Fun "f") [Fun "x"], jOp "_+_" [p, p]]]
  , test' "f if_then_else_ * z"                 [Op "_*_" [jApp (Fun "f") [Op "if_then_else_" [p, p, p]], jF "z"]]
  , test' "f (if_then_else_) * z"               [Op "_*_" [jApp (Fun "f") [Op "if_then_else_" [p, p, p]], jF "z"]]
  , test' "[[_]]"                               [Op "[[_]]" [p]]
  , test' "[[ [[ x ]]* ]]"                      [Op "[[_]]" [jOp "[[_]]*" [jF "x"]]]
  , test' "f [[ g [[ x ]]* ]]"                  [App (Fun "f") [Op "[[_]]" [jApp (Fun "g") [Op "[[_]]*" [jF "x"]]]]]

  , test' (nested nestingDepth)                 [nestedResult nestingDepth]
  , test' (assoc  nestingDepth)                 [assocResult  nestingDepth]

  , test'' 6 2 6
  , test'' 6 1 5
  , test'' 10 1 8
  , test'' 12 2 11
  , test'' 17 1 17
  ]
  where
  -- Some abbreviations.
  w              = WildcardE
  p              = Nothing  -- Placeholder.
  jF             = Just . Fun
  jOp name args  = Just $ Op name args
  jApp expr args = Just $ App expr args

  test' = test exampleClosed example

  nestingDepth = 100

  iterateN n f x = iterate f x !! n

  nested       d = iterateN d (\s -> "x <[ " ++ s ++ " ]>") "x"
  nestedResult d = iterateN d (\x -> Op "_<[_]>" [jF "x", Just x]) (Fun "x")

  assoc       d = iterateN d ("x + " ++) "x"
  assocResult d = iterateN d (\x -> Op "_+_" [Just x, jF "x"]) (Fun "x")

  test'' m i k | not (m >= k && k > i && i > 0) =
                   error "test'': Precondition failed."
               | otherwise =
    test Set.empty (snd $ stressTest m)
         (unwords ["x", op 'a' i, "x", op 'b' k, "x"])
         [Op (op' 'a' i) [ jF "x"
                         , Just $ Op (op' 'b' k) [jF "x", jF "x"]
                         ]]
    where
    op  c i = c : show i
    op' c i = "_" ++ op c i ++ "_"
