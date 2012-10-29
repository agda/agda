{-# LANGUAGE CPP #-}
module Agda.Compiler.MAlonzo.Primitives where

import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as L
import Data.Map as M
import qualified Language.Haskell.Exts.Syntax as HS

import {-# SOURCE #-} Agda.Compiler.MAlonzo.Compiler (term)
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.Utils.Monad
import Agda.Utils.Impossible
import qualified Agda.Utils.HashMap as HMap

#include "../../undefined.h"

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
  | show (qnameName q) /= "main" = ret
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
    mainAlias = HS.FunBind [HS.Match dummy mainLHS [] Nothing mainRHS $ HS.BDecls [] ]
    mainLHS   = HS.Ident "main"
    mainRHS   = HS.UnGuardedRhs $ HS.Var $ HS.UnQual $ unqhname "d" q

-- Haskell modules to be imported for BUILT-INs
importsForPrim :: TCM [HS.ModuleName]
importsForPrim =
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

-- Declarations of helper functions for BUILT-INs
declsForPrim :: TCM [HS.Decl]
declsForPrim = xForPrim $
  [ "NATURAL" |-> (++) <$> natToFrom "Integer" mazNatToInteger mazIntegerToNat
                       <*> natToFrom "Int"     mazNatToInt     mazIntToNat
  , "LIST"   |-> forList mazListToHList mazHListToList
  , "STRING" |-> forList mazListToString mazStringToList
  , "BOOL"   |-> decls ["TRUE", "FALSE"]
       mazBoolToHBool "let { f <<0>> = True; f <<1>> = False; } in f"
       mazHBoolToBool "let { f True = <<0>>; f False = <<1>>; } in f"
  , "CHAR"   |-> return
                 [ fakeDS mazCharToInteger
                   "(fromIntegral . Data.Char.ord :: Char -> Integer)"
                 ]
  ]
  where
    infix 1 |->
    (|->) = (,)
    forList toH toA = decls ["NIL", "CONS"]
       toH (concat
           ["let { f <<0>>        = [];"
           ,"      f (<<1>> x xs) = x : f (" ++ prettyPrint mazCoerce ++ " xs)"
           ,"} in f"])
       toA (concat
           ["let { f []     = <<0>>;"
           ,"      f (c:cs) = <<1>> c (" ++ prettyPrint mazCoerce ++ " (f cs));"
           ,"} in f"])
    natToFrom hty to from = let
        totxt   = repl ["<<0>>", "<<1>>", hty, to] $ concat
                  [ "\\ x -> case x of { <<0>> -> 0 :: <<2>>; "
                  , "<<1>> x -> 1 + (<<3>> (" ++ prettyPrint mazCoerce ++ " x)) }" ]
        fromtxt = repl ["<<0>>", "<<1>>", hty, from] $ concat
                  [ "\\ x -> if x <= (0 :: <<2>>) then <<0>> "
                  , "else <<1>> (" ++ prettyPrint mazCoerce ++ " (<<3>> (x - 1)))" ]
      in do
        ds <- decls ["ZERO", "SUC"] to totxt from fromtxt
        let rule name = HS.Rule name HS.AlwaysActive (Just [HS.RuleVar $ HS.Ident "x"])
            var = HS.Var . HS.UnQual . HS.Ident
            (%) = HS.App
        return $ [HS.RulePragmaDecl dummy
                  [ rule (to ++ "-" ++ from) (var to   % (var from % var "x")) (var "x")
                  , rule (from ++ "-" ++ to) (var from % (var to   % var "x")) (var "x")
                  ]] ++ ds
    decls cs n1 b1 n2 b2 =
      do cs' <- mapM pconName cs
         return $ zipWith (\ n -> fakeDS n . repl cs') [n1, n2] [b1, b2]

mazNatToInteger  = "mazNatToInteger"
mazIntegerToNat  = "mazIntegerToNat"
mazNatToInt      = "mazNatToInt"
mazIntToNat      = "mazIntToNat"
mazCharToInteger = "mazCharToInteger"
mazListToHList   = "mazListToHList"
mazHListToList   = "mazHListToList"
mazListToString  = "mazListToString"
mazStringToList  = "mazStringToList"
mazBoolToHBool   = "mazBoolToHBool"
mazHBoolToBool   = "mazHBoolToBool"

--------------

xForPrim :: [(String, TCM [a])] -> TCM [a]
xForPrim table = do
  qs <- HMap.keys <$> curDefs
  bs <- toList <$> gets stBuiltinThings
  let getName (Builtin (Def q _))    = q
      getName (Builtin (Con q _))    = q
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
  , "primIntegerAbs"     |-> do toN <- bltQual' "NATURAL" mazIntegerToNat
                                return $ repl [toN] $ "\\ x -> <<0>> (abs x)"
  , "primNatToInteger"   |-> bltQual' "NATURAL" mazNatToInteger
  , "primShowInteger"    |-> return "(show :: Integer -> String)"

  -- Natural number functions
  , "primNatPlus"     |-> binNat "(+)"
  , "primNatMinus"    |-> binNat "(-)"
  , "primNatTimes"    |-> binNat "(*)"
  , "primNatDivSuc"   |-> binNat "(\\ x y -> div x (y + 1))"
  , "primNatModSuc"   |-> binNat "(\\ x y -> mod x (y + 1))"
  , "primNatEquality" |-> relNat "(==)"
  , "primNatLess"     |-> relNat "(<)"

  -- Floating point functions
  , "primIntegerToFloat"    |-> return "(fromIntegral :: Integer -> Double)"
  , "primFloatPlus"	    |-> return "((+) :: Double -> Double -> Double)"
  , "primFloatMinus"	    |-> return "((-) :: Double -> Double -> Double)"
  , "primFloatTimes"	    |-> return "((*) :: Double -> Double -> Double)"
  , "primFloatDiv"	    |-> return "((/) :: Double -> Double -> Double)"
  , "primFloatLess"         |-> rel "(<)" "Double"
  , "primRound"	            |-> return "(round :: Double -> Integer)"
  , "primFloor"	            |-> return "(floor :: Double -> Integer)"
  , "primCeiling"	    |-> return "(ceiling :: Double -> Integer)"
  , "primExp"		    |-> return "(exp :: Double -> Double)"
  , "primLog"		    |-> return "(log :: Double -> Double)"  -- partial
  , "primSin"		    |-> return "(sin :: Double -> Double)"
  , "primShowFloat"	    |-> return "(show :: Double -> String)"
  , "primRound"             |-> return "(round :: Double -> Integer)"

  -- Character functions
  , "primCharEquality"   |-> rel "(==)" "Char"
  , "primIsLower"        |-> pred "Data.Char.isLower"
  , "primIsDigit"        |-> pred "Data.Char.isDigit"
  , "primIsAlpha"        |-> pred "Data.Char.isAlpha"
  , "primIsSpace"        |-> pred "Data.Char.isSpace"
  , "primIsAscii"        |-> pred "Data.Char.isAscii"
  , "primIsLatin1"       |-> pred "Data.Char.isLatin1"
  , "primIsPrint"        |-> pred "Data.Char.isPrint"
  , "primIsHexDigit"     |-> pred "Data.Char.isHexDigit"
  , "primToUpper"        |-> return "Data.Char.toUpper"
  , "primToLower"        |-> return "Data.Char.toLower"
  , "primCharToNat" |-> do toN <- bltQual' "NATURAL" mazIntToNat
                           return $ repl [toN] $
                            "(\\ x -> <<0>> ((fromEnum :: Char -> Int) x))"
  , "primNatToChar" |-> do toI <- bltQual' "NATURAL" mazNatToInt
                           return $ repl[toI] $
                            "(\\ x -> (toEnum :: Int -> Char) (<<0>> x))"
  , "primShowChar"  |-> return "(show :: Char -> String)"

  -- String functions
  , "primStringToList"   |-> bltQual' "STRING" mazStringToList
  , "primStringFromList" |-> bltQual' "STRING" mazListToString
  , "primStringAppend"   |-> binAsis "(++)" "String"
  , "primStringEquality" |-> rel "(==)" "String"
  , "primShowString"     |-> return "(show :: String -> String)"

  -- Reflection
  , "primQNameEquality"   |-> rel "(==)" "MAlonzo.RTE.QName () ()"
  , "primQNameType"       |-> return "MAlonzo.RTE.qnameType"
  , "primQNameDefinition" |-> return "MAlonzo.RTE.qnameDefinition"

  , "primDataConstructors" |-> return "(error \"primDataConstructors: not implemented\")"

  -- Trust me
  , ("primTrustMe"       , Right <$> do
       refl <- primRefl
       flip runReaderT 0 $
         term $ lam "a" (lam "A" (lam "x" (lam "y" refl))))
  ]
  where
  x |-> s = (x, Left <$> s)
  bin blt op ty from to = do
    from' <- bltQual' blt from
    to'   <- bltQual' blt to
    return $ repl [op, opty ty, from', to'] $
               "\\ x y -> <<3>> ((<<0>> :: <<1>>) (<<2>> x) (<<2>> y))"
  binNat op = bin "NATURAL" op "Integer" mazNatToInteger mazIntegerToNat
  binAsis op ty = return $ repl [op, opty ty] $ "((<<0>>) :: <<1>>)"
  rel' toTy op ty = do
    toHB <- bltQual' "BOOL" mazHBoolToBool
    return $ repl [op, ty, toHB, toTy] $
      "(\\ x y -> <<2>> ((<<0>> :: <<1>> -> <<1>> -> Bool) (<<3>> x) (<<3>> y)))"
  relNat op = do toHI <- bltQual' "NATURAL" mazNatToInteger
                 rel' toHI op "Integer"
  rel op ty  = rel' "" op ty
  pred p = do toHB <- bltQual' "BOOL" mazHBoolToBool
              return $ repl [p, toHB] $ "(\\ x -> <<1>> (<<0>> x))"
  opty t = t ++ "->" ++ t ++ "->" ++ t
  unimplemented = typeError $ NotImplemented s

  lam x t = Lam Hidden (Abs x t)
{- UNUSED
  var x   = Arg Hidden Relevant (Var x [])
-}

----------------------

repl subs = go where
  go ('<':'<':c:'>':'>':s) | 0 <= i && i < length subs = subs !! i ++ go s
     where i = ord c - ord '0'
  go (c:s) = c : go s
  go []    = []

pconName :: String -> TCM String
pconName s = toS =<< getBuiltin s where
  toS (Con q _) = prettyPrint <$> conhqn q
  toS (Lam _ t) = toS (unAbs t)
  toS _ = mazerror $ "pconName" ++ s

hasCompiledData :: [String] -> TCM Bool
hasCompiledData (s:_) = toB =<< getBuiltin s where
  toB (Con q _)         = do
    def <- getConstInfo =<< ignoreAbstractMode (canonicalName q)
    return $ case compiledHaskell $ defCompiledRep def of
      Just{}  -> True
      Nothing -> False
  toB (Lam _ t) = toB (unAbs t)
  toB _         = return False
hasCompiledData _    = return False


bltQual' b s = prettyPrint <$> bltQual b s
