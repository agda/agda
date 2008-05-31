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
-- One can guarantee polynomial complexity of parsing (for
-- context-free grammars) by, among other things, using a dense
-- representation of ambiguous results. However, the most ambiguous
-- result in the test below has length 2, and I think that we won't
-- encounter very much more than that in practice.

module Main where

import qualified Memoised
import Control.Monad.State hiding (lift)
import PrecedenceGraph hiding (tests)
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

lift :: (s -> s) -> State s ()
lift f = State (\x -> ((), f x))

eq      = Name []    (Just (Infix Non)) ["="]
ltgt    = Name []    (Just (Infix Non)) ["<",">"]
plus    = Name []    (Just (Infix L))   ["+"]
plus'   = Name []    (Just (Infix L))   ["+'"]
minus   = Name []    (Just (Infix R))   ["-"]
mul     = Name []    (Just (Infix L))   ["*"]
div'    = Name []    (Just (Infix L))   ["/"]
pow     = Name []    (Just (Infix R))   ["^"]
or'     = Name []    (Just (Infix R))   ["||"]
not'    = Name []    (Just Prefix)      ["!"]
and'    = Name []    (Just (Infix R))   ["&&"]
eq'     = Name []    (Just (Infix Non)) ["=="]
ite     = Name []    (Just Prefix)      ["if", "then", "else"]
it      = Name []    (Just Prefix)      ["if", "then"]
ox      = Name []    (Just Postfix)     ["<[","]>"]
oxstar  = Name []    (Just Postfix)     ["<[","]>*"]
oxplus  = Name []    (Just Prefix)      ["<[","]>+"]
foo1    = Name ["1"] (Just (Infix L))   ["foo"]
foo2    = Name ["2"] (Just (Infix R))   ["foo"]
llgg    = Name []    (Just (Infix L))   ["<<",">>"]
ggll    = Name []    (Just (Infix Non)) [">>","<<"]
ox'     = Name []    Nothing            ["[[","]]"]
ox'star = Name []    Nothing            ["[[","]]*"]
ox'plus = Name []    Nothing            ["[[","]]+"]

-- Note that this graph is not intended to be representative of how I
-- want operator precedences to be specified for the given operators.

example :: PrecedenceGraph
example = flip execState empty $ mapM lift
  [ unrelated    eq
  , unrelated    ltgt
  , bindsBetween plus   [eq]   []
  , bindsAs      plus'  plus
  , bindsAs      minus  plus
  , bindsBetween mul    [plus] []
  , bindsAs      div'   mul
  , bindsBetween pow    [mul]  []
  , bindsBetween or'    [eq]   []
  , bindsBetween not'   [or']  []
  , bindsBetween and'   [or']  [not', plus]
  , bindsBetween eq'    []     [or']
  , bindsBetween ite    [eq]   [and', mul]
  , bindsAs      it     ite
  , unrelated    ox
  , bindsAs      oxstar ox
  , bindsAs      oxplus ox
  , unrelated    foo1
  , unrelated    foo2
  , unrelated    llgg
  , unrelated    ggll
  ]

exampleClosed :: Set Name
exampleClosed = Set.fromList [ox', ox'star, ox'plus]

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
    toT cs  = NamePart cs

    fix p (Placeholder _ : toks) = Placeholder p : toks
    fix p toks                   = toks

    fixL = fix Beg
    fixR = reverse . fix End . reverse

-- | Parser for identifiers. For simplicity single alphabetic
-- characters are taken as function names, while other character
-- sequences are taken as operator parts.

ident :: NTParser p NT Token => p Name
ident = symbol >>= \s -> case s of
  NamePart n@[c] | isAlpha c -> A.pure (Name [] Nothing [n])
  _                          -> A.empty

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

stressTest :: Integer -> ([Name], PrecedenceGraph)
stressTest n =
  if n <= 0 then let n = stressTestName 0 'n'
                 in  ([n], unrelated n empty)
            else ( topName : names ++ below
                 , flip execState g $ do
                     mapM_ (\n -> lift $ bindsBetween n below []) names
                     lift $ bindsBetween topName (names ++ below) [])
  where
  (below, g) = stressTest (n - 1)
  prev       = stressTestName (pred n) 'n'
  names      = map (stressTestName n) ['a'..'c']
  topName    = stressTestName n 'n'

stressTestName n c = Name [] (Just $ Infix Non) [c : show n]

------------------------------------------------------------------------
-- Tests

tests :: IO Bool
tests = fmap and $ sequence
  [ test' "x"                                   [fun "x"]
  , test' "x = x"                               [Op eq [jF "x", jF "x"]]
  , test' "x = x = x"                           []
  , test' "x < x > x"                           [Op ltgt [jF "x", jF "x", jF "x"]]
  , test' "x < x = x > x"                       [Op ltgt [jF "x", jOp eq [jF "x", jF "x"], jF "x"]]
  , test' "x + x"                               [Op plus [jF "x", jF "x"]]
  , test' "x + y + z"                           [Op plus [jOp plus [jF "x", jF "y"], jF "z"]]
  , test' "x - y"                               [Op minus [jF "x", jF "y"]]
  , test' "x + y - z"                           []
  , test' "x * y / z"                           [Op div' [jOp mul [jF "x", jF "y"], jF "z"]]
  , test' "x * y = z"                           []
  , test' "x ^ y = z"                           []
  , test' "x + y && z"                          [Op and' [jOp plus [jF "x", jF "y"], jF "z"]]
  , test' "x ^ y ^ z"                           [Op pow [jF "x", jOp pow [jF "y", jF "z"]]]
  , test' "! x"                                 [Op not' [jF "x"]]
  , test' "! ! x"                               [Op not' [jOp not' [jF "x"]]]
  , test' "! x + y"                             []
  , test' "! x && y"                            [Op and' [jOp not' [jF "x"], jF "y"]]
  , test' "x <[ x <[ x ]>* ]>"                  [Op ox [jF "x", jOp oxstar [jF "x", jF "x"]]]
  , test' "x <[ x ]> <[ x ]>*"                  [Op oxstar [jOp ox [jF "x", jF "x"], jF "x"]]
  , test' "x << x >> x << x >> x"               [ Op llgg [jF "x", jOp ggll [jF "x", jF "x", jF "x"], jF "x"]
                                                , Op llgg [jOp llgg [jF "x", jF "x", jF "x"], jF "x", jF "x"] ]
  , test' "if x then a else b"                  [Op ite [jF "x", jF "a", jF "b"]]
  , test' "if x then if y then a else b else c" [Op ite [jF "x", jOp ite [jF "y", jF "a", jF "b"], jF "c"]]
  , test' "if x then if y then a else b"        [ Op ite [jF "x", jOp it [jF "y", jF "a"], jF "b"]
                                                , Op it [jF "x", jOp ite [jF "y", jF "a", jF "b"]] ]
  , test' "if x then a + b else c = d"          [Op eq [jOp ite [jF "x", jOp plus [jF "a", jF "b"], jF "c"], jF "d"]]
  , test' "x foo x foo x"                       [ Op foo2 [jF "x", jOp foo2 [jF "x", jF "x"]]
                                                , Op foo1 [jOp foo1 [jF "x", jF "x"], jF "x"] ]
  , test' "x foo x foo x foo x"                 [ Op foo2 [jF "x", jOp foo2 [jF "x", jOp foo2 [jF "x", jF "x"]]]
                                                , Op foo1 [jOp foo1 [jOp foo1 [jF "x", jF "x"], jF "x"], jF "x"] ]
  , test' "_"                                   [w]
  , test' "_+_"                                 [Op plus [p, p]]
  , test' "_ + _"                               [Op plus [Just w, Just w]]
  , test' "if_then a + _ else_ = d"             [Op eq [jOp ite [p, jOp plus [jF "a", Just w], p], jF "d"]]
  , test' "if__then a + _ else_ = d"            []
  , test' "f (_+_)"                             [App (fun "f") [Op plus [p, p]]]
  , test' "(_+_) f"                             [App (Op plus [p, p]) [fun "f"]]
  , test' "f _+_"                               [App (fun "f") [Op plus [p, p]]]
  , test' "f _ +_"                              [Op plus [jApp (fun "f") [w], p]]
  , test' "(((f))) (((x))) (((y)))"             [App (fun "f") [fun "x", fun "y"]]
  , test' "(_)"                                 [w]
  , test' "_<[_]>"                              [Op ox [p, p]]
  , test' "_+ _+'_"                             [Op plus [p, jOp plus' [p, p]]]
  , test' "_+_ +'_"                             [Op plus' [jOp plus [p, p], p]]
  , test' "f (x <[ y ]>) + z"                   [Op plus [jApp (fun "f") [Op ox [jF "x", jF "y"]], jF "z"]]
  , test' "f (_+_ <[ y ]>) + z"                 [Op plus [jApp (fun "f") [Op ox [jOp plus [p, p], jF "y"]], jF "z"]]
  , test' "f (x <[ _+_ ]>) + z"                 [Op plus [jApp (fun "f") [Op ox [jF "x", jOp plus [p, p]]], jF "z"]]
  , test' "f x <[ _+_ ]> + z"                   []
  , test' "f x <[ _+_ ]>"                       [Op ox [jApp (fun "f") [fun "x"], jOp plus [p, p]]]
  , test' "f if_then_else_ * z"                 [Op mul [jApp (fun "f") [Op ite [p, p, p]], jF "z"]]
  , test' "f (if_then_else_) * z"               [Op mul [jApp (fun "f") [Op ite [p, p, p]], jF "z"]]
  , test' "[[_]]"                               [Op ox' [p]]
  , test' "[[ [[ x ]]* ]]"                      [Op ox' [jOp ox'star [jF "x"]]]
  , test' "f [[ g [[ x ]]* ]]"                  [App (fun "f") [Op ox' [jApp (fun "g") [Op ox'star [jF "x"]]]]]

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
  fun s          = Fun (Name [] Nothing [s])
  w              = WildcardE
  p              = Nothing  -- Placeholder.
  jF             = Just . fun
  jOp name args  = Just $ Op name args
  jApp expr args = Just $ App expr args

  test' = test exampleClosed example

  nestingDepth = 100

  iterateN n f x = iterate f x !! n

  nested       d = iterateN d (\s -> "x <[ " ++ s ++ " ]>") "x"
  nestedResult d = iterateN d (\x -> Op ox [jF "x", Just x]) (fun "x")

  assoc       d = iterateN d ("x + " ++) "x"
  assocResult d = iterateN d (\x -> Op plus [Just x, jF "x"]) (fun "x")

  test'' m i k | not (m >= k && k > i && i > 0) =
                   error "test'': Precondition failed."
               | otherwise =
    test Set.empty (snd $ stressTest m)
         (unwords ["x", op i 'a', "x", op k 'b', "x"])
         [Op (stressTestName i 'a')
             [ jF "x"
             , Just $ Op (stressTestName k 'b') [jF "x", jF "x"]
             ]
         ]
    where op i c = c : show i
