module CompilerTest where

-- TODO: Emacs keeps complaining that Test.Tasty.Discover is a member
-- of a hidden package and keeps prompting me to add it to the .cabal-file.
-- Solution M-x haskell-session-change-target -> agda2mlf:test
import qualified Agda.Syntax.Common        as C
import qualified Agda.Syntax.Concrete.Name as C
import           Agda.Syntax.Literal
import           Agda.Syntax.Treeless
import           Compiler
import           Malfunction.AST
import           Test.Tasty
import           Test.Tasty.HUnit
import           Utils
import qualified Data.Map                  as Map

translate'1 :: TTerm -> Term
translate'1 = head . translateTerms' [] . pure

translateTerms' :: [[QName]] -> [TTerm] -> [Term]
translateTerms' qs = translateTerms (mkFakeEnv qs)

translateDef' :: [[QName]] -> QName -> TTerm -> Binding
translateDef' qs = translateDef (mkFakeEnv qs)

mkFakeEnv :: [[QName]] -> Env
mkFakeEnv qs = Env
  { _conMap = Map.unions $ map mkMap qs
  , _level  = 0
  }

mkMap :: [QName] -> Map.Map QName ConRep
mkMap qs = Map.fromList $ zipWith go qs [0..]
  where
    go q i = (q, ConRep i 0)

simpleName :: (C.NameId, String) -> Name
simpleName (idf, concrete) = Name
  { nameId = idf
  , nameConcrete = C.Name undefined [C.Id concrete]
  , nameBindingSite = undefined
  , nameFixity = undefined
  }

simpleQName :: [(C.NameId, String)] -> (C.NameId, String) -> QName
simpleQName mods nm = QName {
  qnameModule = MName (map simpleName mods)
  , qnameName = simpleName nm
  }

simplerQName :: String -> QName
simplerQName s = simpleQName [anId] anId
  where
    anId = (C.NameId 0 0, s)

unitTests :: TestTree
unitTests = testGroup "Compiler unit tests" test_translate

-- TODO: Add this test-case:
-- Agda:
--    f = \ x -> g x
--    g = f
test_translate :: [TestTree]
test_translate =
  -- Tests that the deBruijn index references the *closest* binding.
  [ testCase "sequenced lambda-expressions"
    $   translate'1 (TLam (TLam (TVar 0)))
    @?= Mlambda ["v0", "v1"] (Mvar "v1")
  , testCase "de Bruijn indices" $
    translate'1 (TLam (TApp (TVar 0) [TLam (TVar 1)]))
    @?= Mlambda ["v0"] (Mapply (Mvar "v0") [Mlambda ["v1"] (Mvar "v0")])
  , testCase "factorial" $ translateDef' [] aName (facTT aName) @?= facT aName
  -- This test-case is a bit silly, since `TError TUnreachable` could be encoded
  -- as anything in malfunction. E.g. the function `f : ⊥ -> a` will never be
  -- applied to any arguments!
  , testCase "function from an uninhabited type"
    $ translate'1 (TError TUnreachable)
    @?= Mblock 0 []
  , testCase "fst"
    $ translateDef' [[aName]] aName (fstTT aName) @?= fstT aName
  , testCase "non-nullary constructor application"
    $ runModExample constructorExample
  ]
  where
    aName = simplerQName "someId"

facTT :: QName -> TTerm
facTT qn = TLam (TCase 0 CTNat (TLet (TApp (TPrim PSub)
      [TVar 0,TLit (LitNat undefined 1)]
      ) (TApp (TPrim PMul) [TVar 1,TApp (TDef qn) [TVar 0]])
  ) [TALit {aLit = LitNat undefined 0, aBody = TLit (LitNat undefined 1)}])

facT :: QName -> Binding
facT qn = Recursive [(nameToIdent qn, Mlambda ["v0"]
  (Mswitch (Mvar "v0") [([CaseInt 0],Mint (CBigint 1))
    , ([CaseAnyInt,Deftag],Mlet [Named "v1" (Mintop2 Sub TInt
      (Mvar "v0") (Mint (CBigint 1)))
    ] (Mintop2 Mul TInt (Mvar "v0")
  (Mapply (Mvar (nameToIdent qn)) [Mvar "v1"])))]))]

fstT :: QName -> Binding
fstT qn = Named (nameToIdent qn) (Mlambda ["v0"] (Mswitch (Mvar "v0")
          [([Tag 0],Mlet [Named "v1" (Mfield 0 (Mvar "v0")),Named "v2" (Mint (CBigint 666))]
             (Mvar "v1"))]))
fstTT :: QName -> TTerm
fstTT qn = TLam (TCase 0 (CTData qn)
              (TError TUnreachable) [
                 TACon {aCon = qn, aArity = 2,
                         aBody = TVar 1}])

-- fstTT qcons qdata = TLam (TCase 0 (CTData qdata) (TError TUnreachable)
                          -- [TACon {aCon = qcons, aArity = 2, aBody = TVar 1}])

-- fstT qn = Named (show qn) (Mlambda ["v0"] (Mswitch (Mvar "v0") [([Tag 0],Mlet [Named "v1" (Mfield 0 (Mvar "v0")),Named "v2" (Mint (CInt 0))] (Mvar "v1"))]))

goldenTests :: TestTree
goldenTests = testGroup "Compiler golden tests"
  [ mkGoldenTest "FstSnd" "a"
  , mkGoldenTest "FstSnd" "b"
  , mkGoldenTest "Factorial" "a"
  , mkGoldenTest "Factorial" "b"
  ]

runModExample :: ((Env, [[(QName, TTerm)]]), Mod) -> Assertion
runModExample (inp, expected) = uncurry compile inp @?= expected

constructorExample :: ((Env, [[(QName, TTerm)]]), Mod)
constructorExample = (constructorT zero suc f one, constructorTT zero suc f one)
  where
    zero = simplerQName "zero"
    suc  = simplerQName "suc"
    f    = simplerQName "f"
    one  = simplerQName "one"

constructorT :: QName -> QName -> QName -> QName -> (Env, [[(QName, TTerm)]])
constructorT zero suc fQ oneQ = (env, bindings)
  where
    env = Env (Map.fromList [(zero, ConRep 1 0), (suc, ConRep 0 0)]) 0
    bindings = [[(fQ, f)], [(oneQ, one)]]
    f   = TLam (TApp (TVar 0) [TCon zero])
    one = TApp (TDef fQ) [TCon suc]

constructorTT :: QName -> QName -> QName -> QName -> Mod
constructorTT _zero _suc f one = MMod
  [ Named f'   (Mlambda ["v0"] (Mapply (Mvar "v0") [Mblock 0 []]))
  , Named one' (Mapply (Mvar f') [Mlambda ["a"] (Mblock 1 [Mvar "a"])])
  ] []
  where
    f' = nameToIdent f
    one' = nameToIdent one
