module CompilerTest where

-- TODO: Emacs keeps complaining that Test.Tasty.Discover is a member
-- of a hidden package and keeps prompting me to add it to the .cabal-file.
import Test.Tasty.Discover
import Compiler
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Malfunction.AST

test_translate :: [TestTree]
test_translate =
  -- Tests that the deBruijn index references the *closest* binding.
  [ testCase "sequences lambda-expressions"
    $   translate (TLam (TLam (TVar 0)))
    @?= Mlambda ["v1", "v0"] (Mvar "v0")
-- TODO: Still not sure what this should translate to:
--  , testCase "pattern match constructor"
--    $   translate patternMatchConstructor
--    @?= Mswitch (MVar "v0") [([Tag _], _)]
  ]

-- Please note that this example is incomplete since not all fields
-- in `dummy` fields (that are needed) are instantiated.
patternMatchConstructor :: TTerm
patternMatchConstructor = TCase 0 (CTData typName) (TError TUnreachable) [TACon conName arity body]
  where
    typName, conName :: QName
    -- The name of the data-type
    typName = dummy 0
    -- The name of the constructor for that data-type
    conName  = dummy 1
    dummy :: Int -> QName
    dummy n = QName { qnameName = Name { nameId = toEnum n } }
    -- The arity of the constructor
    arity :: Int
    arity = 2
    -- The body of the case-expression
    body  :: TTerm
    body = TLit $ LitNat (error "Not used, I promise!") 0
