module Agda.Compiler.MAlonzo.Primitives where

import Control.Monad.State
import Data.Char
import Data.List as L
import Data.Map as M
import Language.Haskell.Syntax

import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.Utils.Monad

-- Haskell modules to be imported for BUILT-INs
importsForPrim :: TCM [Module]
importsForPrim = xForPrim $ L.map (\(s, ms)-> (s, return (L.map Module ms))) $
  [ "CHAR" |-> ["Data.Char"]
  -- , "IO" |-> ["System.IO"]
  ]
  where (|->) = (,)


-- Declarations of helper functions for BUILT-INs
declsForPrim :: TCM [HsDecl]
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
       toH "let { f <<0>>        = [];\
                \      f (<<1>> x xs) = x : f (unsafeCoerce xs)\
                \} in f"
       toA "let { f []     = <<0>>;\
                \      f (c:cs) = <<1>> c (unsafeCoerce (f cs));\
                \} in f"
    natToFrom hty to from = let
        totxt   = repl ["<<0>>", "<<1>>", hty] 
                       "let { f <<0>>     = 0 :: <<2>>;\
                            \      f (<<1>> x) = 1 + f (unsafeCoerce x);\
                            \} in f"
        fromtxt = repl ["<<0>>", "<<1>>", hty]
                       "let { f x | x <= (0 :: <<2>>) = <<0>>\
                            \     | True = <<1>> (unsafeCoerce (f (x - 1)))\
                            \} in f"
      in decls ["ZERO", "SUC"] to totxt from fromtxt
    decls cs n1 b1 n2 b2 = 
      ifM (hasCompiledData cs)
          (return $ L.map (`fakeDS` "id") [n1, n2])
        $ do cs' <- mapM pconName cs
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
  qs <- keys   <$> curDefs
  bs <- toList <$> gets stBuiltinThings
  concat <$> sequence [ maybe (return []) id $ L.lookup s table
                        | (s, Builtin (Def q _)) <- bs, q `elem` qs ]


-- Definition bodies for primitive functions
primBody :: String -> TCM HsExp
primBody s = (hsVarUQ . HsIdent <$>) $ maybe unimplemented id $ L.lookup s $ 
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
  , "primIsHExDigit"     |-> pred "Data.Char.isHexDigit"
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
  ]
  where
  (|->) = (,)
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
      "(\\ x y -> <<2>> ((<<0>> :: <<1>> -> <<1>> -> Bool) (<<3>> x) (<<3>> x)))"
  relNat op = do toHI <- bltQual' "NATURAL" mazNatToInteger
                 rel' toHI op "Integer"  
  rel op ty  = rel' "" op ty
  pred p = do toHB <- bltQual' "BOOL" mazHBoolToBool
              return $ repl [p, toHB] $ "(\\ x -> <<1>> (<<0>> x))"
  opty t = t ++ "->" ++ t ++ "->" ++ t
  unimplemented = return$ prettyPrint$ rtmError$ "not yet implemented: "++ s

----------------------

repl subs = go where
  go ('<':'<':c:'>':'>':s) | 0 <= i && i < length subs = subs !! i ++ go s
     where i = ord c - ord '0'
  go (c:s) = c : go s
  go []    = []

pconName :: String -> TCM String
pconName s = toS =<< getBuiltin s where
  toS (Con q _)         = prettyPrint <$> conhqn q
  toS (Lam _ (Abs _ t)) = toS t
  toS _ = mazerror $ "pconName" ++ s

hasCompiledData :: [String] -> TCM Bool
hasCompiledData (s:_) = toB =<< getBuiltin s where
  toB (Con q _)         = do
    def <- getConstInfo =<< ignoreAbstractMode (canonicalName q)
    return $ case theDef def of Constructor{conHsCode = Just _} -> True
                                _                               -> False
  toB (Lam _ (Abs _ t)) = toB t
  toB _                 = return False
hasCompiledData _    = return False
                       

bltQual' b s = prettyPrint <$> bltQual b s

