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

-- TODO: Update test-case to reflect new name-translation-scheme
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
      translateDef' [] qn (facTT qn) @?= facT qn
  -- This test-case is a bit silly, since `TError TUnreachable` could be encoded
  -- as anything in malfunction. E.g. the function `f : ⊥ -> a` will never be
  -- applied to any arguments!
  , testCase "function from an uninhabited type"
    $ translate'1 (TError TUnreachable)
    @?= Mblock 0 []
  , testCase "fst"
    $ let fstqn = simpleQName ["Test"] "fst"
          tupqn = simpleQName ["Test", "Tuple"] "Tup"
      in translateDef' [[tupqn]] fstqn (fstTT fstqn) @?= fstT fstqn
  ]

facTT :: QName -> TTerm
facTT qn = TLam (TCase 0 CTNat (TLet (TApp (TPrim PSub)
      [TVar 0,TLit (LitNat undefined 1)]
      ) (TApp (TPrim PMul) [TVar 1,TApp (TDef qn) [TVar 0]])
  ) [TALit {aLit = LitNat undefined 0, aBody = TLit (LitNat undefined 1)}])

facT :: QName -> Binding
facT qn = Recursive [(show qn, Mlambda ["v0"]
  (Mswitch (Mvar "v0") [([CaseInt 0],Mint (CInt 1))
    , ([CaseAnyInt,Deftag],Mlet [Named "v1" (Mintop2 Sub TInt
      (Mvar "v0") (Mint (CInt 1)))
    ] (Mintop2 Mul TInt (Mvar "v0")
  (Mapply (Mvar (show qn)) [Mvar "v1"])))]))]

fstTT qn = TLam (TCase 0 (CTData qn) (TError TUnreachable) [TACon {aCon = qn, aArity = 2, aBody = TVar 1}])

fstT qn = Named (show qn) (Mlambda ["v0"] (Mswitch (Mvar "v0") [([Tag 0],Mlet [Named "v1" (Mfield 0 (Mvar "v0")),Named "v2" (Mint (CInt 0))] (Mvar "v1"))]))

a = let qn = simpleQName ["Test", "Tuple"] "fst" in
      translateDef' [[qn]] qn (fstTT qn)
