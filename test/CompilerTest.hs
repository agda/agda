module CompilerTest where

-- TODO: Emacs keeps complaining that Test.Tasty.Discover is a member
-- of a hidden package and keeps prompting me to add it to the .cabal-file.
-- Solution M-x haskell-session-change-target -> agda2mlf:test
import qualified Agda.Syntax.Common                 as C
import qualified Agda.Syntax.Concrete.Name          as C
import           Agda.Syntax.Literal
import           Agda.Syntax.Treeless
import qualified Data.Map                           as Map
import           GHC.Word
import           Test.Tasty
import           Test.Tasty.HUnit
import           Utils


import           Agda.Compiler.Malfunction.AST
import           Agda.Compiler.Malfunction.Compiler
import           Agda.Syntax.Common                 (NameId)

type Arity = Int

translate'1 :: TTerm -> Term
translate'1 = head . translateTerms' [] [] . pure

translateTerms' :: [QName] -> [[(QName, Arity)]] -> [TTerm] -> [Term]
translateTerms' ns qs = translateTerms (mkFakeEnv ns qs)

translateDef' :: [QName] -> [[(QName, Arity)]] -> QName -> TTerm -> Binding
translateDef' ns qs = translateDef (mkFakeEnv ns qs)

mkFakeEnv :: [QName] -> [[(QName, Arity)]] -> Env
mkFakeEnv ns cons = mkCompilerEnv ns (Map.unions (map mkMap cons))

mkMap :: [(QName, Arity)] -> Map.Map NameId ConRep
mkMap qs = Map.fromList [ (qnameNameId qn, ConRep i arity)
                        | (i, (qn, arity)) <- zip [0..] qs ]

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
  , testCase "factorial" $ translateDef' [aName] [] aName (facTT aName) @?= facT anIden
  -- This test-case is a bit silly, since `TError TUnreachable` could be encoded
  -- as anything in malfunction. E.g. the function `f : ⊥ -> a` will never be
  -- applied to any arguments!
  , testCase "function from an uninhabited type"
    $ translate'1 (TError TUnreachable)
    @?= wildcardTerm
  -- , testCase "fst"
  --   $ translateDef' [[(aName, 1)]] aName (fstTT aName) @?= fstT aName
  -- This test-case fails for the same reason `fst` fails
  , testCase "non-nullary constructor application"
    $ runModExample constructorExample
  ]
  where
    (aName, anIden) = qnameAndIdent 0 "someId"

facTT :: QName -> TTerm
facTT qn = TLam (TCase 0 CTNat (TLet (TApp (TPrim PSub)
      [TVar 0,TLit (LitNat undefined 1)]
      ) (TApp (TPrim PMul) [TVar 1,TApp (TDef qn) [TVar 0]])
  ) [TALit {aLit = LitNat undefined 0, aBody = TLit (LitNat undefined 1)}])

facT :: Ident -> Binding
facT facIden = Recursive [(facIden, Mlambda ["v0"]
  (Mswitch (Mvar "v0") [([CaseInt 0],Mint (CBigint 1))
    , ([CaseAnyInt,Deftag],Mlet [Named "v1" (Mintop2 Sub TInt
      (Mvar "v0") (Mint (CBigint 1)))
    ] (Mintop2 Mul TInt (Mvar "v0")
  (Mapply (Mvar facIden) [Mvar "v1"])))]))]

-- fstT :: QName -> Binding
-- fstT qn = Named (nameIdToIdent' (qnameNameId qn) "") (Mlambda ["v0"] (Mswitch (Mvar "v0")
--           [([Tag 0],Mlet [Named "v1" (Mfield 0 (Mvar "v0")),Named "v2" (Mint (CBigint 666))]
--              (Mvar "v1"))]))

-- fstTT :: QName -> TTerm
-- fstTT qn = TLam (TCase 0 (CTData qn)
--               (TError TUnreachable) [
--                  TACon {aCon = qn, aArity = 2,
--                          aBody = TVar 1}])

goldenTests :: TestTree
goldenTests = testGroup "Compiler golden tests"
  [ mkGoldenGroup "FstSnd" ["a", "b"]
  , mkGoldenGroup "Factorial" ["a", "b"]
  , mkGoldenGroup "Constructor" ["one", "a"]
  , mkGoldenGroup "Index" ["l0", "l1", "l2"]
  , mkGoldenGroup "Insertion" ["l0", "l1"]
  , mkGoldenGroup "InsertionSort" ["l0", "l1", "l2"]
  ]

runModExample :: ((Env, [(QName, TTerm)]), Mod) -> Assertion
runModExample (inp, expected) = uncurry compile inp @?= expected

constructorExample :: ((Env, [(QName, TTerm)]), Mod)
constructorExample = (constructorTT qzero qsuc qf qone, constructorT if_ ione)
  where
    (qzero, izero) = qnameAndIdent 0 "zero"
    (qsuc, isuc)  = qnameAndIdent 1 "suc"
    (qf, if_)    = qnameAndIdent 2 "f"
    (qone, ione)  = qnameAndIdent 3 "one"

constructorTT :: QName -> QName -> QName -> QName -> (Env, [(QName, TTerm)])
constructorTT zero suc fQ oneQ = (env, bindings)
  where
    env = mkCompilerEnv [zero, suc, fQ, oneQ]
      (Map.fromList [(qnameNameId zero, ConRep 0 0), (qnameNameId suc, ConRep 1 1)])
    bindings = [(fQ, f), (oneQ, one)]
    f   = TLam (TApp (TVar 0) [TCon zero])
    one = TApp (TDef fQ) [TCon suc]

constructorT :: Ident -> Ident -> Mod
constructorT  f one = MMod
  [ Named f   (Mlambda ["v0"] (Mapply (Mvar "v0") [Mblock 0 []]))
  , Named one (Mapply (Mvar f) [Mlambda ["a"] (Mblock 1 [Mvar "a"])])
  ] []

qnameAndIdent :: Word64 -> String -> (QName, Ident)
qnameAndIdent nameid concrete = (simplerQName (nameid, concrete),
                                 nameIdToIdent' (C.NameId 0 nameid) (Just concrete))
  where
    simplerQName :: (Word64, String) -> QName
    simplerQName (sndNameId, concrete) = simpleQName [] (fnameId, concrete)
      where fnameId = C.NameId 0 sndNameId

