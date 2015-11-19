{-# LANGUAGE CPP #-}

module Agda.Compiler.MAlonzo.Primitives where

import Control.Monad.State
import Data.Char
import Data.List as L
import Data.Map as M
import qualified Language.Haskell.Exts.Syntax as HS

import Agda.Compiler.ToTreeless
import {-# SOURCE #-} Agda.Compiler.MAlonzo.Compiler (closedTerm)
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.Utils.Monad
import Agda.Utils.Except
import qualified Agda.Utils.HashMap as HMap

#include "undefined.h"
import Agda.Utils.Impossible

{- OLD
-- | Check that the main function has type IO a, for some a.
checkTypeOfMain :: QName -> Type -> TCM ()
checkTypeOfMain q ty
  | show (qnameName q) /= "main" = return ()
  | otherwise = do
    Def io _ <- ignoreSharing <$> primIO
    ty <- normalise ty
    case ignoreSharing $ unEl ty of
      Def d _ | d == io -> return ()
      _                 -> do
        err <- fsep $
          pwords "The type of main should be" ++
          [prettyTCM io] ++ pwords " A, for some A. The given type is" ++ [prettyTCM ty]
        typeError $ GenericError $ show err
-}

-- | Check that the main function has type IO a, for some a.
checkTypeOfMain :: QName -> Type -> TCM [HS.Decl] -> TCM [HS.Decl]
checkTypeOfMain q ty ret
  | show (nameConcrete $ qnameName q) /= "main" = ret
  | otherwise = do
    Def io _ <- ignoreSharing <$> primIO
    ty <- normalise ty
    case ignoreSharing $ unEl ty of
      Def d _ | d == io -> (mainAlias :) <$> ret
      _                 -> do
        err <- fsep $
          pwords "The type of main should be" ++
          [prettyTCM io] ++ pwords " A, for some A. The given type is" ++ [prettyTCM ty]
        typeError $ GenericError $ show err
  where
    mainAlias = HS.FunBind [HS.Match dummy mainLHS [] Nothing mainRHS emptyBinds ]
    mainLHS   = HS.Ident "main"
    mainRHS   = HS.UnGuardedRhs $ HS.Var $ HS.UnQual $ unqhname "d" q

-- Haskell modules to be imported for BUILT-INs
importsForPrim :: TCM [HS.ModuleName]
importsForPrim =
  fmap (++ [HS.ModuleName "Data.Text"]) $
  xForPrim $
  L.map (\(s, ms) -> (s, return (L.map HS.ModuleName ms))) $
  [ "CHAR"           |-> ["Data.Char"]
  , "primIsDigit"    |-> ["Data.Char"]
  , "primIsLower"    |-> ["Data.Char"]
  , "primIsDigit"    |-> ["Data.Char"]
  , "primIsAlpha"    |-> ["Data.Char"]
  , "primIsSpace"    |-> ["Data.Char"]
  , "primIsAscii"    |-> ["Data.Char"]
  , "primIsLatin1"   |-> ["Data.Char"]
  , "primIsPrint"    |-> ["Data.Char"]
  , "primIsHexDigit" |-> ["Data.Char"]
  , "primToUpper"    |-> ["Data.Char"]
  , "primToLower"    |-> ["Data.Char"]
  ]
  where (|->) = (,)

--------------

xForPrim :: [(String, TCM [a])] -> TCM [a]
xForPrim table = do
  qs <- HMap.keys <$> curDefs
  bs <- toList <$> gets stBuiltinThings
  let getName (Builtin (Def q _))    = q
      getName (Builtin (Con q _))    = conName q
      getName (Builtin (Shared p))   = getName (Builtin $ derefPtr p)
      getName (Builtin _)            = __IMPOSSIBLE__
      getName (Prim (PrimFun q _ _)) = q
  concat <$> sequence [ maybe (return []) id $ L.lookup s table
                        | (s, def) <- bs, getName def `elem` qs ]


-- Definition bodies for primitive functions
primBody :: String -> TCM HS.Exp
primBody s = maybe unimplemented (either (hsVarUQ . HS.Ident) id <$>) $
             L.lookup s $
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

  -- Natural number functions
  , "primNatPlus"      |-> binNat "(+)"
  , "primNatMinus"     |-> binNat "(\\ x y -> max 0 (x - y))"
  , "primNatTimes"     |-> binNat "(*)"
  , "primNatDivSucAux" |-> binNat4 "(\\ k m n j -> k + div (max 0 $ n + m - j) (m + 1))"
  , "primNatModSucAux" |-> binNat4 "(\\ k m n j -> if n > j then mod (n - j - 1) (m + 1) else (k + n))"
  , "primNatEquality"  |-> relNat "(==)"
  , "primNatLess"      |-> relNat "(<)"

  -- Floating point functions
  , "primNatToFloat"        |-> return "(fromIntegral :: Integer -> Double)"
  , "primFloatPlus"         |-> return "((+) :: Double -> Double -> Double)"
  , "primFloatMinus"        |-> return "((-) :: Double -> Double -> Double)"
  , "primFloatTimes"        |-> return "((*) :: Double -> Double -> Double)"
  , "primFloatDiv"          |-> return "((/) :: Double -> Double -> Double)"
  , "primFloatEquality"     |-> return "((\\ x y -> if isNaN x && isNaN y then True else x == y) :: Double -> Double -> Bool)"
  , "primFloatLess"         |-> return (unwords
                                  [ "((\\ x y ->"
                                  , "let isNegInf z = z < 0 && isInfinite z in"
                                  , "if isNegInf y then False else"
                                  , "if isNegInf x then True  else"
                                  , "if isNaN x    then True  else"
                                  , "x < y) :: Double -> Double -> Bool)" ])
  , "primFloatSqrt"         |-> return "(sqrt :: Double -> Double)"
  , "primRound"             |-> return "(round :: Double -> Integer)"
  , "primFloor"             |-> return "(floor :: Double -> Integer)"
  , "primCeiling"           |-> return "(ceiling :: Double -> Integer)"
  , "primExp"               |-> return "(exp :: Double -> Double)"
  , "primLog"               |-> return "(log :: Double -> Double)"
  , "primSin"               |-> return "(sin :: Double -> Double)"
  , "primShowFloat"         |-> return "(Data.Text.pack . (\\ x -> if isNegativeZero x then \"0.0\" else show x) :: Double -> Data.Text.Text)"

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

  -- String functions
  , "primStringToList"   |-> return "Data.Text.unpack"
  , "primStringFromList" |-> return "Data.Text.pack"
  , "primStringAppend"   |-> binAsis "Data.Text.append" "Data.Text.Text"
  , "primStringEquality" |-> rel "(==)" "Data.Text.Text"
  , "primShowString"     |-> return "Data.Text.unpack"

  -- Reflection
  , "primQNameEquality"   |-> rel "(==)" "MAlonzo.RTE.QName () ()"
  , "primQNameLess"       |-> rel "(<)" "MAlonzo.RTE.QName () ()"
  , "primShowQName"       |-> return "Data.Text.pack . MAlonzo.RTE.qnameString"
  , "primQNameType"       |-> return "MAlonzo.RTE.qnameType"
  , "primQNameDefinition" |-> return "MAlonzo.RTE.qnameDefinition"

  , "primDataConstructors" |-> return "(error \"primDataConstructors: not implemented\")"
  , "primDataNumberOfParameters" |-> return "(error \"primDataNumberOfParameters: not implemented\")"

  -- Seq
  , "primForce"      |-> return "\\ _ _ _ _ x f -> f $! x"
  , "primForceLemma" |-> return "erased"

  -- Trust me
  , ("primTrustMe"       , Right <$> do
       refl <- primRefl
       closedTerm =<< (closedTermToTreeless $ lam "a" (lam "A" (lam "x" (lam "y" refl)))))
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
  unimplemented = typeError $ NotImplemented s

  lam x t = Lam (setHiding Hidden defaultArgInfo) (Abs x t)

noCheckCover :: QName -> TCM Bool
noCheckCover q = (||) <$> isBuiltin q builtinNat <*> isBuiltin q builtinInteger

----------------------

repl :: [String] -> String -> String
repl subs = go where
  go ('<':'<':c:'>':'>':s) | 0 <= i && i < length subs = subs !! i ++ go s
     where i = ord c - ord '0'
  go (c:s) = c : go s
  go []    = []

pconName :: String -> TCM String
pconName s = toS . ignoreSharing =<< getBuiltin s where
  toS (Con q _) = prettyPrint <$> conhqn (conName q)
  toS (Lam _ t) = toS (unAbs t)
  toS _ = mazerror $ "pconName" ++ s

bltQual' :: String -> String -> TCM String
bltQual' b s = prettyPrint <$> bltQual b s
