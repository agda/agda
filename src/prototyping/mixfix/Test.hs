------------------------------------------------------------------------
-- Tests the performance and correctness of the precedence handling
------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

-- Summary: The memoising CPS parser seems to be fast enough.
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
-- result in the test below has length 3, and I think that we won't
-- encounter very much more than that in practice.

module Main where

import qualified ExpressionParser as Expr
import Parser
import PrecedenceGraph hiding (tests)
import Name            hiding (tests)
import Expression      hiding (tests)
import Token           hiding (tests)

import Control.Monad.State hiding (lift)
import Data.Char
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Function
import qualified Control.Applicative as A
import Prelude hiding (lex)

------------------------------------------------------------------------
-- Test driver

test :: Set Name -> Set Name -> PrecedenceGraph ->
        String -> [Expr] -> IO Bool
test closed names g s es = case Token.lex s of
  Nothing -> do
    putStrLn $ "Lex error: " ++ show s
    return (es == [])
  Just ts -> do
    let es'     = Expr.parse g (lookupName names) closed ts
        correct = sort es' == sort es
        isOK    = if correct then "OK" else "Not OK"
    putStrLn $ pad 40 (show s) ++ pad 8 (isOK ++ ": ")
                               ++ pad 90 (show es')
    return correct
  where
  pad n s = take n s ++ replicate (n - length s) ' ' ++ " "

main = do
  ok <- tests
  putStrLn $ if ok then "All tests passed."
                   else "Some test failed."

------------------------------------------------------------------------
-- Example precedence graph

lift :: (s -> s) -> State s ()
lift f = state (\x -> ((), f x))

eq      = Name []    (Just Infix)   ["="]
ltgt    = Name []    (Just Infix)   ["<",">"]
plus    = Name []    (Just Infix)   ["+"]
plus'   = Name []    (Just Infix)   ["+'"]
minus   = Name []    (Just Infix)   ["-"]
mul     = Name []    (Just Infix)   ["*"]
div'    = Name []    (Just Infix)   ["/"]
pow     = Name []    (Just Infix)   ["^"]
or'     = Name []    (Just Infix)   ["||"]
not'    = Name []    (Just Prefix)  ["!"]
and'    = Name []    (Just Infix)   ["&&"]
eq'     = Name []    (Just Infix)   ["=="]
ite     = Name []    (Just Prefix)  ["if", "then", "else"]
it      = Name []    (Just Prefix)  ["if", "then"]
ox      = Name []    (Just Postfix) ["<[","]>"]
oxstar  = Name []    (Just Postfix) ["<[","]>*"]
oxplus  = Name []    (Just Prefix)  ["<[","]>+"]
foo1    = Name ["1"] (Just Infix)   ["foo"]
foo2    = Name ["2"] (Just Infix)   ["foo"]
llgg    = Name []    (Just Infix)   ["<<",">>"]
ggll    = Name []    (Just Infix)   [">>","<<"]
ox'     = Name []    Nothing        ["[[","]]"]
ox'star = Name []    Nothing        ["[[","]]*"]
ox'plus = Name []    Nothing        ["[[","]]+"]
plusC   = Name []    (Just Infix)   ["+C"]
mulC    = Name []    (Just Infix)   ["*C"]
pair    = Name []    (Just Infix)   [","]
pairR   = Name []    (Just Prefix)  [","]

-- Note that this graph is not intended to be representative of how I
-- want operator precedences to be specified for the given operators.

example :: PrecedenceGraph
example = flip execState empty $ mapM lift
  [ unrelated    eq     Non
  , unrelated    ltgt   Non
  , bindsBetween plus   L   [eq]   []
  , bindsAs      plus'  L   plus
  , bindsAs      minus  R   plus
  , bindsBetween mul    L   [plus] []
  , bindsAs      div'   L   mul
  , bindsBetween pow    R   [mul]  []
  , bindsBetween or'    R   [eq]   []
  , bindsBetween not'   Non [or']  []
  , bindsBetween and'   R   [or']  [not', plus]
  , bindsBetween eq'    Non []     [or']
  , bindsBetween ite    Non [eq]   [and', mul]
  , bindsAs      it     Non ite
  , unrelated    ox     Non
  , bindsAs      oxstar Non ox
  , bindsAs      oxplus Non ox
  , unrelated    foo1   L
  , unrelated    foo2   R
  , unrelated    llgg   L
  , unrelated    ggll   Non
  , unrelated    plusC  Non
  , bindsBetween mulC   Non [plusC] [plusC]
  , unrelated    pair   R
  , bindsAs      pairR  Non pair
  ]

exampleClosed = Set.fromList [ox', ox'star, ox'plus]

exampleNames = Set.unions $
  Map.elems (allOperators example) ++
  [ exampleClosed
  , Set.fromList $
      map (Name [] Nothing . (: []))
          ["x", "y", "z", "a", "b", "c", "d", "g"] ++
      [Name ["M"] Nothing ["f"]]
  ]

------------------------------------------------------------------------
-- Looking up names

-- | A smarter data structure should be used here.

lookupName :: Set Name -> Name -> Set Name
lookupName names n = Set.filter p names
  where
  p n' = n == n' { moduleName = drop (length mn' - length mn) mn' }
    where
    mn  = moduleName n
    mn' = moduleName n'

------------------------------------------------------------------------
-- A demanding graph

-- stressTest False n yields a graph which is the transitive closure
-- of a graph with the following shape (with edges going upwards):
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
-- The top-most node is n_n. stressTest True n is the union of
-- stressTest False n and its converse.

stressTest :: Bool -> Integer -> ([Name], PrecedenceGraph)
stressTest bidir i =
  if i <= 0 then
    let n = stressTestName 0 'n'
    in  ([n], unrelated n Non empty)
  else ( topName : names ++ below
       , flip execState g $ do
           mapM_ (\n -> lift $ bindsBetween' n Non below) names
           lift $ bindsBetween' topName Non (names ++ below)
       )
  where
  (below, g) = stressTest bidir (i - 1)
  prev       = stressTestName (i - 1) 'n'
  names      = map (stressTestName i) ['a'..'c']
  topName    = stressTestName i 'n'

  bindsBetween' o a t = bindsBetween o a t (if bidir then t else [])

stressTestName i c = Name [] (Just Infix) [c : show i]

stressTestNames :: Integer -> Set Name
stressTestNames n = Set.fromList $
  Name [] Nothing ["x"] :
  stressTestName 0 'n' :
  [ stressTestName i c | i <- [1 .. n], c <- "abcn" ]

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
  , test' "x 1.foo x 1.foo x"                   [Op foo1 [jOp foo1 [jF "x", jF "x"], jF "x"]]
  , test' "x 1.foo x 2.foo x"                   []
  , test' "1._foo_"                             [Op foo1 [p, p]]
  , test' "2._foo_"                             [Op foo2 [p, p]]
  , test' "x 1.foo_"                            [Op foo1 [jF "x", p]]
  , test' "1._foo x"                            [Op foo1 [p, jF "x"]]
  , test' "_1.foo x"                            []
  , test' "_"                                   [w]
  , test' "_+_"                                 [Op plus [p, p]]
  , test' "_ + _"                               [Op plus [Just w, Just w]]
  , test' "if_then a + _ else_ = d"             [Op eq [jOp ite [p, jOp plus [jF "a", Just w], p], jF "d"]]
  , test' "if__then a + _ else_ = d"            []
  , test' "f (_+_)"                             [app funMf [Op plus [p, p]]]
  , test' "(_+_) f"                             [app (Op plus [p, p]) [funMf]]
  , test' "f _+_"                               [app funMf [Op plus [p, p]]]
  , test' "f _ +_"                              [Op plus [jApp funMf [w], p]]
  , test' "(((f))) (((x))) (((y)))"             [app funMf [fun "x", fun "y"]]
  , test' "(_)"                                 [w]
  , test' "_<[_]>"                              [Op ox [p, p]]
  , test' "_+ _+'_"                             [Op plus [p, jOp plus' [p, p]]]
  , test' "_+_ +'_"                             [Op plus' [jOp plus [p, p], p]]
  , test' "f (x <[ y ]>) + z"                   [Op plus [jApp funMf [Op ox [jF "x", jF "y"]], jF "z"]]
  , test' "f (_+_ <[ y ]>) + z"                 [Op plus [jApp funMf [Op ox [jOp plus [p, p], jF "y"]], jF "z"]]
  , test' "f (x <[ _+_ ]>) + z"                 [Op plus [jApp funMf [Op ox [jF "x", jOp plus [p, p]]], jF "z"]]
  , test' "f x <[ _+_ ]> + z"                   []
  , test' "f x <[ _+_ ]>"                       [Op ox [jApp funMf [fun "x"], jOp plus [p, p]]]
  , test' "f if_then_else_ * z"                 [Op mul [jApp funMf [Op ite [p, p, p]], jF "z"]]
  , test' "f (if_then_else_) * z"               [Op mul [jApp funMf [Op ite [p, p, p]], jF "z"]]
  , test' "[[_]]"                               [Op ox' [p]]
  , test' "[[ [[ x ]]* ]]"                      [Op ox' [jOp ox'star [jF "x"]]]
  , test' "f [[ g [[ x ]]* ]]"                  [app funMf [Op ox' [jApp (fun "g") [Op ox'star [jF "x"]]]]]
  , test' "x +C y *C z"                         [ Op plusC [jF "x", jOp mulC [jF "y", jF "z"]]
                                                , Op mulC [jOp plusC [jF "x", jF "y"], jF "z"] ]
  , test' "a +C b *C c +C d"                    [ Op plusC [jF "a", jOp mulC [jF "b", jOp plusC [jF "c", jF "d"]]]
                                                , Op mulC [jOp plusC [jF "a", jF "b"], jOp plusC [jF "c", jF "d"]]
                                                , Op plusC [jOp mulC [jOp plusC [jF "a", jF "b"], jF "c"], jF "d"] ]
  , test' ", x , , , y"                         [Op pairR [jOp pair [jF "x", jOp pairR [jOp pairR [jF "y"]]]]]

  , test' (nested nestingDepth)                 [nestedResult nestingDepth]
  , test' (assoc  nestingDepth)                 [assocResult  nestingDepth]

  , test'' False 6 2 6
  , test'' False 6 1 5
  , test'' False 10 1 8
  , test'' False 12 2 11
  , test'' False 17 1 17

  , test'' True 6 1 6
  , test'' True 6 6 1
  , test'' True 17 1 17
  ]
  where
  -- Some abbreviations.
  fun s          = Fun (Name [] Nothing [s])
  funMf          = Fun (Name ["M"] Nothing ["f"])
  w              = WildcardE
  p              = Nothing  -- Placeholder.
  jF             = Just . fun
  jOp name args  = Just $ Op name args
  jApp expr args = Just $ app expr args

  test' = test exampleClosed exampleNames example

  nestingDepth = 100

  iterateN n f x = iterate f x !! n

  nested       d = iterateN d (\s -> "x <[ " ++ s ++ " ]>") "x"
  nestedResult d = iterateN d (\x -> Op ox [jF "x", Just x]) (fun "x")

  assoc       d = iterateN d ("x + " ++) "x"
  assocResult d = iterateN d (\x -> Op plus [Just x, jF "x"]) (fun "x")

  test'' bidir m i k
    | not (if bidir then m >= max i k && min i k > 0
                    else m >= k && k > i && i > 0) =
        error "test'': Precondition failed."
    | otherwise =
    test Set.empty
         (stressTestNames m)
         (snd $ stressTest bidir m)
         (unwords ["x", op i 'a', "x", op k 'b', "x"])
         (Op (stressTestName i 'a')
             [ jF "x"
             , Just $ Op (stressTestName k 'b') [jF "x", jF "x"]
             ] :
          if bidir then
            [Op (stressTestName k 'b')
                [ Just $ Op (stressTestName i 'a') [jF "x", jF "x"]
                , jF "x"
                ]
            ]
          else
            [])
    where op i c = c : show i
