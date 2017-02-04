module CompilerTest where

-- TODO: Emacs keeps complaining that Test.Tasty.Discover is a member
-- of a hidden package and keeps prompting me to add it to the .cabal-file.
-- Solution M-x haskell-session-change-target -> agda2mlf:test
import Test.Tasty.Discover
import Compiler
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Malfunction.AST
import qualified Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Common as C

translate'1 :: TTerm -> Term
translate'1 = head . translate' [] . pure

simpleName :: String -> Name
simpleName name = Name {
  nameId = C.NameId 0 0 -- NOTE: we don't use this but it has an unpacked type so it cannot be undefined
  , nameConcrete = C.Name undefined [C.Id name]
  , nameBindingSite = undefined
  , nameFixity = undefined
  }

simpleQName :: [String] -> String -> QName
simpleQName mods nm = QName {
  qnameModule = MName (map simpleName mods)
  , qnameName = simpleName nm
  }

test_translate :: [TestTree]
test_translate =
  -- Tests that the deBruijn index references the *closest* binding.
  [ testCase "sequences lambda-expressions"
    $   translate'1 (TLam (TLam (TVar 0)))
    @?= Mlambda ["v0", "v1"] (Mvar "v1")
  , testCase "de Bruijn indices" $
    translate'1 (TLam (TApp (TVar 0) [TLam (TVar 1)]))
    @?= Mlambda ["v0"] (Mapply (Mvar "v0") [Mlambda ["v1"] (Mvar "v0")])
  , testCase "factorial" $ let qn = simpleQName ["Test"] "fact" in
      translateDef' [] qn
      (TLam (TCase 0 CTNat (TLet (TApp (TPrim PSub) [TVar 0,TLit (LitNat undefined 1)]) (TApp (TPrim PMul) [TVar 1,TApp (TDef qn) [TVar 0]])) [TALit {aLit = LitNat undefined 0, aBody = TLit (LitNat undefined 1)}]))
    @?= Recursive [("Test.fact",Mlambda ["v0"] (Mswitch (Mvar "v0") [([CaseInt 0],Mint (CInt 1)), ([CaseAnyInt,Deftag],Mlet [Named "v1" (Mintop2 Sub TInt (Mvar "v0") (Mint (CInt 1)))] (Mintop2 Mul TInt (Mvar "v0") (Mapply (Mvar "Test.fact") [Mvar "v1"])))]))]
-- TODO: Still not sure what this should translate to:
--  , testCase "pattern match constructor"
--    $   translate patternMatchConstructor
--    @?= Mswitch (MVar "v0") [([Tag _], _)]
  ]

-- Please note that this example is incomplete since not all fields
-- in `dummy` fields (that are needed) are instantiated.
-- patternMatchConstructor :: TTerm
-- patternMatchConstructor = TCase 0 (CTData typName) (TError TUnreachable) [TACon conName arity body]
--   where
--     typName, conName :: QName
--     -- The name of the data-type
--     typName = dummy 0
--     -- The name of the constructor for that data-type
--     conName  = dummy 1
--     dummy :: Int -> QName
--     dummy n = QName { qnameName = Name { nameId = toEnum n } }
--     -- The arity of the constructor
--     arity :: Int
--     arity = 2
--     -- The body of the case-expression
--     body  :: TTerm
--     body = TLit $ LitNat (error "Not used, I promise!") 0
