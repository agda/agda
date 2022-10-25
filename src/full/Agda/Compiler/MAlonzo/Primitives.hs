
module Agda.Compiler.MAlonzo.Primitives where

import Control.Arrow ( second )
import Control.Monad.Trans.Maybe ( MaybeT(MaybeT, runMaybeT) )

import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap
import Data.Maybe
import qualified Data.Text as T

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Lens
import Agda.Utils.List   (hasElem)
import Agda.Utils.Maybe
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Haskell.Syntax as HS

import Agda.Utils.Impossible

newtype MainFunctionDef = MainFunctionDef Definition

data CheckedMainFunctionDef = CheckedMainFunctionDef
  { checkedMainDef :: MainFunctionDef
  , checkedMainDecl :: HS.Decl
  }

-- Andreas, 2019-04-29, issue #3731: exclude certain kinds of names, like constructors.
-- TODO: Also only consider top-level definition (not buried inside a module).
asMainFunctionDef :: Definition -> Maybe MainFunctionDef
asMainFunctionDef d = case (theDef d) of
    Axiom{}                              -> perhaps
    Function{ funProjection = Left _ }   -> perhaps
    Function{ funProjection = Right{}  } -> no
    AbstractDefn{}                       -> no
    GeneralizableVar{}                   -> no
    DataOrRecSig{}                       -> no
    Datatype{}                           -> no
    Record{}                             -> no
    Constructor{}                        -> no
    Primitive{}                          -> no
    PrimitiveSort{}                      -> no
  where
  isNamedMain = "main" == prettyShow (nameConcrete . qnameName . defName $ d)  -- ignores the qualification!?
  perhaps | isNamedMain = Just $ MainFunctionDef d
          | otherwise   = no
  no                    = Nothing

mainFunctionDefs :: Interface -> [MainFunctionDef]
mainFunctionDefs i = catMaybes $ asMainFunctionDef <$> defs
  where
    defs = HMap.elems $ iSignature i ^. sigDefinitions

-- | Check that the main function has type IO a, for some a.
checkTypeOfMain :: Definition -> HsCompileM (Maybe CheckedMainFunctionDef)
checkTypeOfMain def = runMaybeT $ do
  -- Only indicate main functions in the main module.
  isMainModule <- curIsMainModule
  mainDef <- MaybeT $ pure $ if isMainModule then asMainFunctionDef def else Nothing
  liftTCM $ checkTypeOfMain' mainDef

checkTypeOfMain' :: MainFunctionDef -> TCM CheckedMainFunctionDef
checkTypeOfMain' m@(MainFunctionDef def) = CheckedMainFunctionDef m <$> do
    Def io _ <- primIO
    ty <- reduce $ defType def
    case unEl ty of
      Def d _ | d == io -> return mainAlias
      _                 -> do
        err <- fsep $
          pwords "The type of main should be" ++
          [prettyTCM io] ++ pwords " A, for some A. The given type is" ++ [prettyTCM ty]
        typeError $ GenericError $ show err
  where
    mainAlias = HS.FunBind [HS.Match mainLHS [] mainRHS emptyBinds ]
    mainLHS   = HS.Ident "main"
    mainRHS   = HS.UnGuardedRhs $ HS.App mazCoerce (HS.Var $ HS.UnQual $ dname $ defName def)

treelessPrimName :: TPrim -> String
treelessPrimName p =
  case p of
    PQuot   -> "quotInt"
    PRem    -> "remInt"
    PSub    -> "subInt"
    PAdd    -> "addInt"
    PMul    -> "mulInt"
    PGeq    -> "geqInt"
    PLt     -> "ltInt"
    PEqI    -> "eqInt"
    PQuot64 -> "quot64"
    PRem64  -> "rem64"
    PSub64  -> "sub64"
    PAdd64  -> "add64"
    PMul64  -> "mul64"
    PLt64   -> "lt64"
    PEq64   -> "eq64"
    PITo64  -> "word64FromNat"
    P64ToI  -> "word64ToNat"
    PEqF    -> "MAlonzo.RTE.Float.doubleDenotEq"
    -- MAlonzo uses literal patterns, so we don't need equality for the other primitive types
    PEqC    -> __IMPOSSIBLE__
    PEqS    -> __IMPOSSIBLE__
    PEqQ    -> __IMPOSSIBLE__
    PSeq    -> "seq"
    -- primitives only used by GuardsToPrims transformation, which MAlonzo doesn't use
    PIf     -> __IMPOSSIBLE__

-- | Haskell modules to be imported for BUILT-INs
importsForPrim :: BuiltinThings PrimFun -> [Definition] -> [HS.ModuleName]
importsForPrim builtinThings defs = xForPrim table builtinThings defs ++ [HS.ModuleName "Data.Text"]
  where
  table = Map.fromDistinctAscList $ map (second HS.ModuleName)
    -- KEEP THIS LIST IN ALPHABETICAL ORDER!
    -- Otherwise, Map.fromDistinctAscList will produce garbage.
    [ "CHAR"                       |-> "Data.Char"
    , "primFloatCeiling"           |-> "MAlonzo.RTE.Float"
    , "primFloatDecode"            |-> "MAlonzo.RTE.Float"
    , "primFloatEncode"            |-> "MAlonzo.RTE.Float"
    , "primFloatEquality"          |-> "MAlonzo.RTE.Float"
    , "primFloatFloor"             |-> "MAlonzo.RTE.Float"
    , "primFloatInequality"        |-> "MAlonzo.RTE.Float"
    , "primFloatIsSafeInteger"     |-> "MAlonzo.RTE.Float"
    , "primFloatLess"              |-> "MAlonzo.RTE.Float"
    , "primFloatRound"             |-> "MAlonzo.RTE.Float"
    , "primFloatToRatio"           |-> "MAlonzo.RTE.Float"
    , "primFloatToWord64"          |-> "MAlonzo.RTE.Float"
    , "primIsAlpha"                |-> "Data.Char"
    , "primIsAscii"                |-> "Data.Char"
    , "primIsDigit"                |-> "Data.Char"
    , "primIsHexDigit"             |-> "Data.Char"
    , "primIsLatin1"               |-> "Data.Char"
    , "primIsLower"                |-> "Data.Char"
    , "primIsPrint"                |-> "Data.Char"
    , "primIsSpace"                |-> "Data.Char"
    , "primRatioToFloat"           |-> "MAlonzo.RTE.Float"
    , "primToLower"                |-> "Data.Char"
    , "primToUpper"                |-> "Data.Char"
    ]
  (|->) = (,)

--------------

xForPrim :: Map String a -> BuiltinThings PrimFun -> [Definition] -> [a]
xForPrim table builtinThings defs = catMaybes
    [ Map.lookup s table
    | (s, def) <- Map.toList builtinThings
    , maybe False elemDefs $ getName def
    ]
  where
  elemDefs = hasElem $ map defName defs
  getName = \case
    Builtin t                 -> Just $ getPrimName t
    Prim (PrimFun q _ _)      -> Just q
    BuiltinRewriteRelations _ -> Nothing


-- | Definition bodies for primitive functions
primBody :: MonadTCError m => String -> m HS.Exp
primBody s = maybe unimplemented (fromRight (hsVarUQ . HS.Ident) <$>) $
             List.lookup s $
  [
  -- Integer functions
    "primIntegerPlus"    |-> binAsis "(+)" "Integer"
  , "primIntegerMinus"   |-> binAsis "(-)" "Integer"
  , "primIntegerTimes"   |-> binAsis "(*)" "Integer"
  , "primIntegerDiv"     |-> binAsis "div" "Integer"
  , "primIntegerMod"     |-> binAsis "mod" "Integer"
  , "primIntegerEquality"|-> rel "(==)" "Integer"
  , "primIntegerLess"    |-> rel "(<)"  "Integer"
  , "primIntegerAbs"     |-> return "(abs :: Integer -> Integer)"
  , "primNatToInteger"   |-> return "(id :: Integer -> Integer)"
  , "primShowInteger"    |-> return "(Data.Text.pack . show :: Integer -> Data.Text.Text)"

  -- Levels
  , "primLevelZero"   |-> return "()"
  , "primLevelSuc"    |-> return "(\\ _ -> ())"
  , "primLevelMax"    |-> return "(\\ _ _ -> ())"

  -- Sorts
  , "primSetOmega"    |-> return "()"
  , "primStrictSet"   |-> return "\\ _ -> ()"

  -- Natural number functions
  , "primNatPlus"      |-> binNat "(+)"
  , "primNatMinus"     |-> binNat "(\\ x y -> max 0 (x - y))"
  , "primNatTimes"     |-> binNat "(*)"
  , "primNatDivSucAux" |-> binNat4 "(\\ k m n j -> k + div (max 0 $ n + m - j) (m + 1))"
  , "primNatModSucAux" |-> binNat4 "(\\ k m n j -> if n > j then mod (n - j - 1) (m + 1) else (k + n))"
  , "primNatEquality"  |-> relNat "(==)"
  , "primNatLess"      |-> relNat "(<)"
  , "primShowNat"      |-> return "(Data.Text.pack . show :: Integer -> Data.Text.Text)"

  -- Machine word functions
  , "primWord64ToNat"   |-> return "MAlonzo.RTE.word64ToNat"
  , "primWord64FromNat" |-> return "MAlonzo.RTE.word64FromNat"
  , "primWord64ToNatInjective" |-> return mazErasedName

  -- Floating point functions
  , "primFloatEquality"          |-> return "MAlonzo.RTE.Float.doubleEq"
  , "primFloatInequality"        |-> return "MAlonzo.RTE.Float.doubleLe"
  , "primFloatLess"              |-> return "MAlonzo.RTE.Float.doubleLt"
  , "primFloatIsInfinite"        |-> return "(isInfinite :: Double -> Bool)"
  , "primFloatIsNaN"             |-> return "(isNaN :: Double -> Bool)"
  , "primFloatIsNegativeZero"    |-> return "(isNegativeZero :: Double -> Bool)"
  , "primFloatIsSafeInteger"     |-> return "MAlonzo.RTE.Float.isSafeInteger"
  , "primFloatToWord64"          |-> return "MAlonzo.RTE.Float.doubleToWord64"
  , "primFloatToWord64Injective" |-> return mazErasedName
  , "primNatToFloat"             |-> return "(MAlonzo.RTE.Float.intToDouble :: Integer -> Double)"
  , "primIntToFloat"             |-> return "(MAlonzo.RTE.Float.intToDouble :: Integer -> Double)"
  , "primFloatRound"             |-> return "MAlonzo.RTE.Float.doubleRound"
  , "primFloatFloor"             |-> return "MAlonzo.RTE.Float.doubleFloor"
  , "primFloatCeiling"           |-> return "MAlonzo.RTE.Float.doubleCeiling"
  , "primFloatToRatio"           |-> return "MAlonzo.RTE.Float.doubleToRatio"
  , "primRatioToFloat"           |-> return "MAlonzo.RTE.Float.ratioToDouble"
  , "primFloatDecode"            |-> return "MAlonzo.RTE.Float.doubleDecode"
  , "primFloatEncode"            |-> return "MAlonzo.RTE.Float.doubleEncode"
  , "primShowFloat"              |-> return "(Data.Text.pack . show :: Double -> Data.Text.Text)"
  , "primFloatPlus"              |-> return "MAlonzo.RTE.Float.doublePlus"
  , "primFloatMinus"             |-> return "MAlonzo.RTE.Float.doubleMinus"
  , "primFloatTimes"             |-> return "MAlonzo.RTE.Float.doubleTimes"
  , "primFloatNegate"            |-> return "MAlonzo.RTE.Float.doubleNegate"
  , "primFloatDiv"               |-> return "MAlonzo.RTE.Float.doubleDiv"
  , "primFloatPow"               |-> return "MAlonzo.RTE.Float.doublePow"
  , "primFloatSqrt"              |-> return "MAlonzo.RTE.Float.doubleSqrt"
  , "primFloatExp"               |-> return "MAlonzo.RTE.Float.doubleExp"
  , "primFloatLog"               |-> return "MAlonzo.RTE.Float.doubleLog"
  , "primFloatSin"               |-> return "MAlonzo.RTE.Float.doubleSin"
  , "primFloatCos"               |-> return "MAlonzo.RTE.Float.doubleCos"
  , "primFloatTan"               |-> return "MAlonzo.RTE.Float.doubleTan"
  , "primFloatASin"              |-> return "MAlonzo.RTE.Float.doubleASin"
  , "primFloatACos"              |-> return "MAlonzo.RTE.Float.doubleACos"
  , "primFloatATan"              |-> return "MAlonzo.RTE.Float.doubleATan"
  , "primFloatATan2"             |-> return "MAlonzo.RTE.Float.doubleATan2"
  , "primFloatSinh"              |-> return "MAlonzo.RTE.Float.doubleSinh"
  , "primFloatCosh"              |-> return "MAlonzo.RTE.Float.doubleCosh"
  , "primFloatTanh"              |-> return "MAlonzo.RTE.Float.doubleTanh"
  , "primFloatASinh"             |-> return "MAlonzo.RTE.Float.doubleASinh"
  , "primFloatACosh"             |-> return "MAlonzo.RTE.Float.doubleACosh"
  , "primFloatATanh"             |-> return "MAlonzo.RTE.Float.doubleATanh"

  -- Character functions
  , "primCharEquality"   |-> rel "(==)" "Char"
  , "primIsLower"        |-> return "Data.Char.isLower"
  , "primIsDigit"        |-> return "Data.Char.isDigit"
  , "primIsAlpha"        |-> return "Data.Char.isAlpha"
  , "primIsSpace"        |-> return "Data.Char.isSpace"
  , "primIsAscii"        |-> return "Data.Char.isAscii"
  , "primIsLatin1"       |-> return "Data.Char.isLatin1"
  , "primIsPrint"        |-> return "Data.Char.isPrint"
  , "primIsHexDigit"     |-> return "Data.Char.isHexDigit"
  , "primToUpper"        |-> return "Data.Char.toUpper"
  , "primToLower"        |-> return "Data.Char.toLower"
  , "primCharToNat" |-> return "(fromIntegral . fromEnum :: Char -> Integer)"
  , "primNatToChar" |-> return "MAlonzo.RTE.natToChar"
  , "primShowChar"  |-> return "(Data.Text.pack . show :: Char -> Data.Text.Text)"
  , "primCharToNatInjective" |-> return mazErasedName

  -- String functions
  , "primStringUncons"   |-> return "Data.Text.uncons"
  , "primStringToList"   |-> return "Data.Text.unpack"
  , "primStringFromList" |-> return "Data.Text.pack"
  , "primStringAppend"   |-> binAsis "Data.Text.append" "Data.Text.Text"
  , "primStringEquality" |-> rel "(==)" "Data.Text.Text"
  , "primShowString"     |-> return "(Data.Text.pack . show :: Data.Text.Text -> Data.Text.Text)"
  , "primStringToListInjective" |-> return mazErasedName
  , "primStringFromListInjective" |-> return mazErasedName

  -- Reflection
  , "primQNameEquality"   |-> rel "(==)" "MAlonzo.RTE.QName"
  , "primQNameLess"       |-> rel "(<)" "MAlonzo.RTE.QName"
  , "primShowQName"       |-> return "Data.Text.pack . MAlonzo.RTE.qnameString"
  , "primQNameFixity"     |-> return "MAlonzo.RTE.qnameFixity"
  , "primQNameToWord64s"  |-> return "\\ qn -> (MAlonzo.RTE.nameId qn, MAlonzo.RTE.moduleId qn)"
  , "primQNameToWord64sInjective" |-> return mazErasedName
  , "primMetaEquality"    |-> rel "(==)" "Integer"
  , "primMetaLess"        |-> rel "(<)" "Integer"
  , "primShowMeta"        |-> return "\\ x -> Data.Text.pack (\"_\" ++ show (x :: Integer))"
  , "primMetaToNat"       |-> return "(id :: Integer -> Integer)"
  , "primMetaToNatInjective" |-> return mazErasedName

  -- Seq
  , "primForce"      |-> return "\\ _ _ _ _ x f -> f $! x"
  , "primForceLemma" |-> return mazErasedName

  -- Erase
  , "primEraseEquality" |-> return mazErasedName

  -- Cubical
  , builtinIMin       |-> return "(&&)"
  , builtinIMax       |-> return "(||)"
  , builtinINeg       |-> return "not"
  , "primPartial"     |-> return "\\_ _ x -> x"
  , "primPartialP"    |-> return "\\_ _ x -> x"
  , builtinPOr        |-> return "\\_ i _ _ x y -> if i then x else y"
  , builtinComp       |-> return "\\_ _ _ _ x -> x"
  , builtinTrans      |-> return "\\_ _ _ x -> x"
  , builtinHComp      |-> return "\\_ _ _ _ x -> x"
  , builtinSubOut     |-> return "\\_ _ _ _ x -> x"
  , builtin_glueU     |-> return "\\_ _ _ _ _ x -> x"
  , builtin_unglueU   |-> return "\\_ _ _ _ x -> x"
  , builtinFaceForall |-> return
                            "\\f -> f True == True && f False == True"
  , "primDepIMin"     |-> return "\\i f -> if i then f () else False"
  , "primIdFace"      |-> return "\\_ _ _ _ -> fst"
  , "primIdPath"      |-> return "\\_ _ _ _ -> snd"
  , builtinIdElim     |-> return
                            "\\_ _ _ _ _ f x y -> f (fst y) x (snd y)"
  ]
  where
  x |-> s = (x, Left <$> s)
  binNat  op = return $ repl [op] "(<<0>> :: Integer -> Integer -> Integer)"
  binNat4 op = return $ repl [op] "(<<0>> :: Integer -> Integer -> Integer -> Integer -> Integer)"
  binAsis op ty = return $ repl [op, opty ty] $ "((<<0>>) :: <<1>>)"
  rel' toTy op ty = do
    return $ repl [op, ty, toTy] $
      "(\\ x y -> (<<0>> :: <<1>> -> <<1>> -> Bool) (<<2>> x) (<<2>> y))"
  relNat op = do
    return $ repl [op] $
      "(<<0>> :: Integer -> Integer -> Bool)"
  rel op ty  = rel' "" op ty
  opty t = t ++ "->" ++ t ++ "->" ++ t
  unimplemented = typeError $ NotImplemented s

  hLam x t = Lam (setHiding Hidden defaultArgInfo) (Abs x t)
  nLam x t = Lam (setHiding NotHidden defaultArgInfo) (Abs x t)

noCheckCover :: (HasBuiltins m, MonadReduce m) => QName -> m Bool
noCheckCover q = (||) <$> isBuiltin q builtinNat <*> isBuiltin q builtinInteger

----------------------

bltQual' :: String -> String -> HsCompileM String
bltQual' b s = prettyPrint <$> bltQual b s
