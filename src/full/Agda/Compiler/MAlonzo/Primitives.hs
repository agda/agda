
module Agda.Compiler.MAlonzo.Primitives where

import Control.Monad.State
import Data.Char
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import {-# SOURCE #-} Agda.Compiler.MAlonzo.Compiler (closedTerm)
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.HashMap as HMap
import qualified Agda.Utils.Haskell.Syntax as HS

import Agda.Utils.Impossible

-- Andreas, 2019-04-29, issue #3731: exclude certain kinds of names, like constructors.
-- TODO: Also only consider top-level definition (not buried inside a module).
isMainFunction :: QName -> Defn -> Bool
isMainFunction q = \case
    Axiom{}                             -> perhaps
    Function{ funProjection = Nothing } -> perhaps
    Function{ funProjection = Just{}  } -> no
    AbstractDefn{}                      -> no
    GeneralizableVar{}                  -> no
    DataOrRecSig{}                      -> no
    Datatype{}                          -> no
    Record{}                            -> no
    Constructor{}                       -> no
    Primitive{}                         -> no
  where
  perhaps = "main" == prettyShow (nameConcrete $ qnameName q)  -- ignores the qualification!?
  no      = False

-- | Check for "main" function, but only in the main module.
hasMainFunction
  :: IsMain    -- ^ Are we looking at the main module?
  -> Interface -- ^ The module.
  -> IsMain    -- ^ Did we find a "main" function?
hasMainFunction NotMain _ = NotMain
hasMainFunction IsMain i
  | List.any (\ (x, def) -> isMainFunction x $ theDef def) names = IsMain
  | otherwise = NotMain
  where
    names = HMap.toList $ iSignature i ^. sigDefinitions

-- | Check that the main function has type IO a, for some a.
checkTypeOfMain :: IsMain -> QName -> Definition -> TCM [HS.Decl] -> TCM [HS.Decl]
checkTypeOfMain NotMain q def ret = ret
checkTypeOfMain  IsMain q def ret
  | not (isMainFunction q $ theDef def) = ret
  | otherwise = do
    Def io _ <- primIO
    ty <- normalise $ defType def
    case unEl ty of
      Def d _ | d == io -> (mainAlias :) <$> ret
      _                 -> do
        err <- fsep $
          pwords "The type of main should be" ++
          [prettyTCM io] ++ pwords " A, for some A. The given type is" ++ [prettyTCM ty]
        typeError $ GenericError $ show err
  where
    mainAlias = HS.FunBind [HS.Match mainLHS [] mainRHS emptyBinds ]
    mainLHS   = HS.Ident "main"
    mainRHS   = HS.UnGuardedRhs $ HS.App mazCoerce (HS.Var $ HS.UnQual $ unqhname "d" q)

treelessPrimName :: TPrim -> String
treelessPrimName p =
  case p of
    PQuot -> "quotInt"
    PRem  -> "remInt"
    PSub  -> "subInt"
    PAdd  -> "addInt"
    PMul  -> "mulInt"
    PGeq  -> "geqInt"
    PLt   -> "ltInt"
    PEqI  -> "eqInt"
    PQuot64 -> "quot64"
    PRem64  -> "rem64"
    PSub64  -> "sub64"
    PAdd64  -> "add64"
    PMul64  -> "mul64"
    PLt64   -> "lt64"
    PEq64  -> "eq64"
    PITo64 -> "word64FromNat"
    P64ToI -> "word64ToNat"
    PEqF  -> "eqFloat"
    -- MAlonzo uses literal patterns, so we don't need equality for the other primitive types
    PEqC  -> __IMPOSSIBLE__
    PEqS  -> __IMPOSSIBLE__
    PEqQ  -> __IMPOSSIBLE__
    PSeq  -> "seq"
    -- primitives only used by GuardsToPrims transformation, which MAlonzo doesn't use
    PIf   -> __IMPOSSIBLE__

-- | Haskell modules to be imported for BUILT-INs
importsForPrim :: TCM [HS.ModuleName]
importsForPrim =
  fmap (++ [HS.ModuleName "Data.Text"]) $
  xForPrim $
  List.map (\(s, ms) -> (s, return (List.map HS.ModuleName ms))) $
  [ "CHAR"              |-> ["Data.Char"]
  , "primIsAlpha"       |-> ["Data.Char"]
  , "primIsAscii"       |-> ["Data.Char"]
  , "primIsDigit"       |-> ["Data.Char"]
  , "primIsHexDigit"    |-> ["Data.Char"]
  , "primIsLatin1"      |-> ["Data.Char"]
  , "primIsLower"       |-> ["Data.Char"]
  , "primIsPrint"       |-> ["Data.Char"]
  , "primIsSpace"       |-> ["Data.Char"]
  , "primToLower"       |-> ["Data.Char"]
  , "primToUpper"       |-> ["Data.Char"]
  ]
  where (|->) = (,)

--------------

xForPrim :: [(String, TCM [a])] -> TCM [a]
xForPrim table = do
  qs <- HMap.keys <$> curDefs
  bs <- Map.toList <$> getsTC stBuiltinThings
  let getName (Builtin (Def q _))    = q
      getName (Builtin (Con q _ _))  = conName q
      getName (Builtin (Lam _ b))    = getName (Builtin $ unAbs b)
      getName (Builtin _)            = __IMPOSSIBLE__
      getName (Prim (PrimFun q _ _)) = q
  concat <$> sequence [ fromMaybe (return []) $ List.lookup s table
                        | (s, def) <- bs, getName def `elem` qs ]


-- | Definition bodies for primitive functions
primBody :: String -> TCM HS.Exp
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
  , "primWord64ToNatInjective" |-> return "erased"

  -- Floating point functions
  , "primNatToFloat"        |-> return "(fromIntegral :: Integer -> Double)"
  , "primFloatPlus"         |-> return "((+)          :: Double -> Double -> Double)"
  , "primFloatMinus"        |-> return "((-)          :: Double -> Double -> Double)"
  , "primFloatTimes"        |-> return "((*)          :: Double -> Double -> Double)"
  , "primFloatNegate"       |-> return "(negate       :: Double -> Double)"
  , "primFloatDiv"          |-> return "((/)          :: Double -> Double -> Double)"
  -- ASR (2016-09-14). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  , "primFloatEquality"          |-> return "MAlonzo.RTE.eqFloat"
  , "primFloatLess"              |-> return "MAlonzo.RTE.ltFloat"
  , "primFloatNumericalEquality" |-> return "MAlonzo.RTE.eqNumFloat"
  , "primFloatNumericalLess"     |-> return "MAlonzo.RTE.ltNumFloat"
  , "primFloatSqrt"         |-> return "(sqrt :: Double -> Double)"
  , "primRound"             |-> return "(round . MAlonzo.RTE.normaliseNaN :: Double -> Integer)"
  , "primFloor"             |-> return "(floor . MAlonzo.RTE.normaliseNaN :: Double -> Integer)"
  , "primCeiling"           |-> return "(ceiling . MAlonzo.RTE.normaliseNaN :: Double -> Integer)"
  , "primExp"               |-> return "(exp :: Double -> Double)"
  , "primLog"               |-> return "(log :: Double -> Double)"
  , "primSin"               |-> return "(sin :: Double -> Double)"
  , "primCos"               |-> return "(cos :: Double -> Double)"
  , "primTan"               |-> return "(tan :: Double -> Double)"
  , "primASin"              |-> return "(asin :: Double -> Double)"
  , "primACos"              |-> return "(acos :: Double -> Double)"
  , "primATan"              |-> return "(atan :: Double -> Double)"
  , "primATan2"             |-> return "(atan2 :: Double -> Double -> Double)"
  , "primShowFloat"         |-> return "(Data.Text.pack . show :: Double -> Data.Text.Text)"
  , "primFloatToWord64"     |-> return "MAlonzo.RTE.doubleToWord64"
  , "primFloatToWord64Injective" |-> return "erased"

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
  , "primNatToChar" |-> return "(toEnum . fromIntegral :: Integer -> Char)"
  , "primShowChar"  |-> return "(Data.Text.pack . show :: Char -> Data.Text.Text)"
  , "primCharToNatInjective" |-> return "erased"

  -- String functions
  , "primStringToList"   |-> return "Data.Text.unpack"
  , "primStringFromList" |-> return "Data.Text.pack"
  , "primStringAppend"   |-> binAsis "Data.Text.append" "Data.Text.Text"
  , "primStringEquality" |-> rel "(==)" "Data.Text.Text"
  , "primShowString"     |-> return "(Data.Text.pack . show :: Data.Text.Text -> Data.Text.Text)"
  , "primStringToListInjective" |-> return "erased"

  -- Reflection
  , "primQNameEquality"   |-> rel "(==)" "MAlonzo.RTE.QName"
  , "primQNameLess"       |-> rel "(<)" "MAlonzo.RTE.QName"
  , "primShowQName"       |-> return "Data.Text.pack . MAlonzo.RTE.qnameString"
  , "primQNameFixity"     |-> return "MAlonzo.RTE.qnameFixity"
  , "primQNameToWord64s"  |-> return "\\ qn -> (MAlonzo.RTE.nameId qn, MAlonzo.RTE.moduleId qn)"
  , "primQNameToWord64sInjective" |-> return "erased"
  , "primMetaEquality"    |-> rel "(==)" "Integer"
  , "primMetaLess"        |-> rel "(<)" "Integer"
  , "primShowMeta"        |-> return "\\ x -> Data.Text.pack (\"_\" ++ show (x :: Integer))"
  , "primMetaToNat"       |-> return "(id :: Integer -> Integer)"
  , "primMetaToNatInjective" |-> return "erased"

  -- Seq
  , "primForce"      |-> return "\\ _ _ _ _ x f -> f $! x"
  , "primForceLemma" |-> return "erased"

  -- Erase
  , ("primEraseEquality", Right <$> do
       refl <- primRefl
       let erase = hLam "a" $ hLam "A" $ hLam "x" $ hLam "y" $ nLam "eq" refl
       closedTerm =<< closedTermToTreeless LazyEvaluation erase
    )
  ]
  where
  x |-> s = (x, Left <$> s)
  bin blt op ty from to = do
    from' <- bltQual' blt from
    to'   <- bltQual' blt to
    return $ repl [op, opty ty, from', to'] $
               "\\ x y -> <<3>> ((<<0>> :: <<1>>) (<<2>> x) (<<2>> y))"
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
  axiom_prims = ["primIMin","primIMax","primINeg","primPartial","primPartialP","primPFrom1","primPOr","primComp"]
  unimplemented | s `List.elem` axiom_prims = return $ rtmError $ "primitive with no body evaluated: " ++ s
                | otherwise = typeError $ NotImplemented s

  hLam x t = Lam (setHiding Hidden defaultArgInfo) (Abs x t)
  nLam x t = Lam (setHiding NotHidden defaultArgInfo) (Abs x t)

noCheckCover :: QName -> TCM Bool
noCheckCover q = (||) <$> isBuiltin q builtinNat <*> isBuiltin q builtinInteger

----------------------


pconName :: String -> TCM String
pconName s = toS =<< getBuiltin s where
  toS (Con q _ _) = prettyPrint <$> conhqn (conName q)
  toS (Lam _ t) = toS (unAbs t)
  toS _ = mazerror $ "pconName" ++ s

bltQual' :: String -> String -> TCM String
bltQual' b s = prettyPrint <$> bltQual b s
