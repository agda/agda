module CompilerTest where

import Test.Tasty.Discover
import Compiler
import Agda.Syntax.Treeless
import Malfunction.AST

test_translate :: [TestTree]
test_translate =
  [
    testCase "translate" $
    translate (TLam (TLam (TVar 0))) @?= (Mlambda ["v1"] (Mlambda ["v0"] (Mvar "v0")))
  ]
