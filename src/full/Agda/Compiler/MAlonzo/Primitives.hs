{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.MAlonzo.Primitives where

import Control.Arrow ( second )
import Control.Monad.Trans.Maybe ( MaybeT(MaybeT, runMaybeT) )

import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Maybe

import Agda.Compiler.Common
import Agda.Compiler.MAlonzo.Misc
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal
import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Lens
import Agda.Utils.List   (hasElem)
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
  table = Map.fromList $ map (second HS.ModuleName)
    [ someBuiltin BuiltinChar                |-> "Data.Char"
    , someBuiltin PrimFloatCeiling           |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatDecode            |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatEncode            |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatEquality          |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatFloor             |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatInequality        |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatIsSafeInteger     |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatLess              |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatRound             |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatToRatio           |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimFloatToWord64          |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimIsAlpha                |-> "Data.Char"
    , someBuiltin PrimIsAscii                |-> "Data.Char"
    , someBuiltin PrimIsDigit                |-> "Data.Char"
    , someBuiltin PrimIsHexDigit             |-> "Data.Char"
    , someBuiltin PrimIsLatin1               |-> "Data.Char"
    , someBuiltin PrimIsLower                |-> "Data.Char"
    , someBuiltin PrimIsPrint                |-> "Data.Char"
    , someBuiltin PrimIsSpace                |-> "Data.Char"
    , someBuiltin PrimRatioToFloat           |-> "MAlonzo.RTE.Float"
    , someBuiltin PrimToLower                |-> "Data.Char"
    , someBuiltin PrimToUpper                |-> "Data.Char"
    ]
  (|->) = (,)

--------------

xForPrim :: Map SomeBuiltin a -> BuiltinThings PrimFun -> [Definition] -> [a]
xForPrim table builtinThings defs = catMaybes
    [ Map.lookup s table
    | (s, def) <- Map.toList builtinThings
    , maybe False elemDefs $ getName def
    ]
  where
  elemDefs = hasElem $ map defName defs
  getName = \case
    Builtin t                 -> Just $ getPrimName t
    Prim (PrimFun q _ _ _)    -> Just q
    BuiltinRewriteRelations _ -> Nothing


-- | Definition bodies for primitive functions
primBody :: MonadTCError m => PrimitiveId -> m HS.Exp
primBody s = maybe unimplemented (fromRight (hsVarUQ . HS.Ident) <$>) $ List.lookup s $
  [
  -- Integer functions
    PrimShowInteger      |-> return "(Data.Text.pack . show :: Integer -> Data.Text.Text)"

  -- Levels
  , PrimLevelZero        |-> return "()"
  , PrimLevelSuc         |-> return "(\\ _ -> ())"
  , PrimLevelMax         |-> return "(\\ _ _ -> ())"

  -- Natural number functions
  , PrimNatPlus         |-> binNat "(+)"
  , PrimNatMinus        |-> binNat "(\\ x y -> max 0 (x - y))"
  , PrimNatTimes        |-> binNat "(*)"
  , PrimNatDivSucAux    |-> binNat4 "(\\ k m n j -> k + div (max 0 $ n + m - j) (m + 1))"
  , PrimNatModSucAux    |-> binNat4 "(\\ k m n j -> if n > j then mod (n - j - 1) (m + 1) else (k + n))"
  , PrimNatEquality     |-> relNat "(==)"
  , PrimNatLess         |-> relNat "(<)"
  , PrimShowNat         |-> return "(Data.Text.pack . show :: Integer -> Data.Text.Text)"

  -- Machine word functions
  , PrimWord64ToNat     |-> return "MAlonzo.RTE.word64ToNat"
  , PrimWord64FromNat   |-> return "MAlonzo.RTE.word64FromNat"
  , PrimWord64ToNatInjective   |-> return mazErasedName

  -- Floating point functions
  , PrimFloatEquality            |-> return "MAlonzo.RTE.Float.doubleEq"
  , PrimFloatInequality          |-> return "MAlonzo.RTE.Float.doubleLe"
  , PrimFloatLess                |-> return "MAlonzo.RTE.Float.doubleLt"
  , PrimFloatIsInfinite          |-> return "(isInfinite :: Double -> Bool)"
  , PrimFloatIsNaN               |-> return "(isNaN :: Double -> Bool)"
  , PrimFloatIsNegativeZero      |-> return "(isNegativeZero :: Double -> Bool)"
  , PrimFloatIsSafeInteger       |-> return "MAlonzo.RTE.Float.isSafeInteger"
  , PrimFloatToWord64            |-> return "MAlonzo.RTE.Float.doubleToWord64"
  , PrimFloatToWord64Injective   |-> return mazErasedName
  , PrimNatToFloat               |-> return "(MAlonzo.RTE.Float.intToDouble :: Integer -> Double)"
  , PrimIntToFloat               |-> return "(MAlonzo.RTE.Float.intToDouble :: Integer -> Double)"
  , PrimFloatRound               |-> return "MAlonzo.RTE.Float.doubleRound"
  , PrimFloatFloor               |-> return "MAlonzo.RTE.Float.doubleFloor"
  , PrimFloatCeiling             |-> return "MAlonzo.RTE.Float.doubleCeiling"
  , PrimFloatToRatio             |-> return "MAlonzo.RTE.Float.doubleToRatio"
  , PrimRatioToFloat             |-> return "MAlonzo.RTE.Float.ratioToDouble"
  , PrimFloatDecode              |-> return "MAlonzo.RTE.Float.doubleDecode"
  , PrimFloatEncode              |-> return "MAlonzo.RTE.Float.doubleEncode"
  , PrimShowFloat                |-> return "(Data.Text.pack . show :: Double -> Data.Text.Text)"
  , PrimFloatPlus                |-> return "MAlonzo.RTE.Float.doublePlus"
  , PrimFloatMinus               |-> return "MAlonzo.RTE.Float.doubleMinus"
  , PrimFloatTimes               |-> return "MAlonzo.RTE.Float.doubleTimes"
  , PrimFloatNegate              |-> return "MAlonzo.RTE.Float.doubleNegate"
  , PrimFloatDiv                 |-> return "MAlonzo.RTE.Float.doubleDiv"
  , PrimFloatPow                 |-> return "MAlonzo.RTE.Float.doublePow"
  , PrimFloatSqrt                |-> return "MAlonzo.RTE.Float.doubleSqrt"
  , PrimFloatExp                 |-> return "MAlonzo.RTE.Float.doubleExp"
  , PrimFloatLog                 |-> return "MAlonzo.RTE.Float.doubleLog"
  , PrimFloatSin                 |-> return "MAlonzo.RTE.Float.doubleSin"
  , PrimFloatCos                 |-> return "MAlonzo.RTE.Float.doubleCos"
  , PrimFloatTan                 |-> return "MAlonzo.RTE.Float.doubleTan"
  , PrimFloatASin                |-> return "MAlonzo.RTE.Float.doubleASin"
  , PrimFloatACos                |-> return "MAlonzo.RTE.Float.doubleACos"
  , PrimFloatATan                |-> return "MAlonzo.RTE.Float.doubleATan"
  , PrimFloatATan2               |-> return "MAlonzo.RTE.Float.doubleATan2"
  , PrimFloatSinh                |-> return "MAlonzo.RTE.Float.doubleSinh"
  , PrimFloatCosh                |-> return "MAlonzo.RTE.Float.doubleCosh"
  , PrimFloatTanh                |-> return "MAlonzo.RTE.Float.doubleTanh"
  , PrimFloatASinh               |-> return "MAlonzo.RTE.Float.doubleASinh"
  , PrimFloatACosh               |-> return "MAlonzo.RTE.Float.doubleACosh"
  , PrimFloatATanh               |-> return "MAlonzo.RTE.Float.doubleATanh"

  -- Character functions
  , PrimCharEquality     |-> rel "(==)" "Char"
  , PrimIsLower          |-> return "Data.Char.isLower"
  , PrimIsDigit          |-> return "Data.Char.isDigit"
  , PrimIsAlpha          |-> return "Data.Char.isAlpha"
  , PrimIsSpace          |-> return "Data.Char.isSpace"
  , PrimIsAscii          |-> return "Data.Char.isAscii"
  , PrimIsLatin1         |-> return "Data.Char.isLatin1"
  , PrimIsPrint          |-> return "Data.Char.isPrint"
  , PrimIsHexDigit       |-> return "Data.Char.isHexDigit"
  , PrimToUpper          |-> return "Data.Char.toUpper"
  , PrimToLower          |-> return "Data.Char.toLower"
  , PrimCharToNat   |-> return "(fromIntegral . fromEnum :: Char -> Integer)"
  , PrimNatToChar   |-> return "MAlonzo.RTE.natToChar"
  , PrimShowChar    |-> return "(Data.Text.pack . show :: Char -> Data.Text.Text)"
  , PrimCharToNatInjective   |-> return mazErasedName

  -- String functions
  , PrimStringUncons     |-> return "Data.Text.uncons"
  , PrimStringToList     |-> return "Data.Text.unpack"
  , PrimStringFromList   |-> return "Data.Text.pack"
  , PrimStringAppend     |-> binAsis "Data.Text.append" "Data.Text.Text"
  , PrimStringEquality   |-> rel "(==)" "Data.Text.Text"
  , PrimShowString       |-> return "(Data.Text.pack . show :: Data.Text.Text -> Data.Text.Text)"
  , PrimStringToListInjective   |-> return mazErasedName
  , PrimStringFromListInjective   |-> return mazErasedName

  -- Reflection
  , PrimQNameEquality     |-> rel "(==)" "MAlonzo.RTE.QName"
  , PrimQNameLess         |-> rel "(<)" "MAlonzo.RTE.QName"
  , PrimShowQName         |-> return "Data.Text.pack . MAlonzo.RTE.qnameString"
  , PrimQNameFixity       |-> return "MAlonzo.RTE.qnameFixity"
  , PrimQNameToWord64s    |-> return "\\ qn -> (MAlonzo.RTE.nameId qn, MAlonzo.RTE.moduleId qn)"
  , PrimQNameToWord64sInjective   |-> return mazErasedName
  , PrimMetaEquality      |-> rel "(==)" "(Integer, Integer)"
  , PrimMetaLess          |-> rel "(<)" "(Integer, Integer)"
  -- Should be kept in sync with version in `primitiveFunctions` in
  -- Agda.TypeChecking.Primitive
  , PrimShowMeta          |-> return "\\ (m, h) -> Data.Text.pack (\"_\" ++ show (m :: Integer) ++ \"@\" ++ show (h :: Integer))"
  -- Should be kept in sync with `metaToNat` in Agda.TypeChecking.Primitive
  , PrimMetaToNat         |-> return "\\ (m, h) -> (h :: Integer) * 2^64 + (m :: Integer)"
  , PrimMetaToNatInjective   |-> return mazErasedName

  -- Seq
  , PrimForce        |-> return "\\ _ _ _ _ x f -> f $! x"
  , PrimForceLemma   |-> return mazErasedName

  -- Lock universe
  , PrimLockUniv |-> return "()"

  -- Erase
  , PrimEraseEquality |-> return mazErasedName

  -- Cubical
  , PrimIMin          |-> return "(&&)"
  , PrimIMax          |-> return "(||)"
  , PrimINeg          |-> return "not"
  , PrimPartial       |-> return "\\_ _ x -> x"
  , PrimPartialP      |-> return "\\_ _ x -> x"
  , PrimPOr           |-> return "\\_ i _ _ x y -> if i then x else y"
  , PrimComp          |-> return "\\_ _ _ _ x -> x"
  , PrimTrans         |-> return "\\_ _ _ x -> x"
  , PrimHComp         |-> return "\\_ _ _ _ x -> x"
  , PrimSubOut        |-> return "\\_ _ _ _ x -> x"
  , Prim_glueU        |-> return "\\_ _ _ _ _ x -> x"
  , Prim_unglueU      |-> return "\\_ _ _ _ x -> x"
  , PrimFaceForall    |-> return
                            "\\f -> f True == True && f False == True"
  , PrimDepIMin       |-> return "\\i f -> if i then f () else False"
  , PrimIdFace        |-> return "\\_ _ _ _ -> fst"
  , PrimIdPath        |-> return "\\_ _ _ _ -> snd"
  , PrimIdElim        |-> return
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
  unimplemented = typeError $ NotImplemented (getBuiltinId s)

  hLam x t = Lam (setHiding Hidden defaultArgInfo) (Abs x t)
  nLam x t = Lam (setHiding NotHidden defaultArgInfo) (Abs x t)

noCheckCover :: (HasBuiltins m, MonadReduce m) => QName -> m Bool
noCheckCover q = (||) <$> isBuiltin q builtinNat <*> isBuiltin q builtinInteger
