module CompilerTest where

import Test.Tasty.Discover
import Compiler
import Agda.Syntax.Treeless
import Malfunction.AST

test_translate :: [TestTree]
test_translate =
  -- Tests that the deBruijn index references the *closest* binding.
  [ testCase "translate"
    $   translate (TLam (TLam (TVar 0)))
    @?= Mlambda ["v1", "v0"] (Mvar "v0")
  ]
