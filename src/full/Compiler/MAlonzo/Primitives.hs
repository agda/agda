module Compiler.MAlonzo.Primitives where

import Control.Monad.State
import Data.Char
import Data.List as L
import Data.Map as M
import Language.Haskell.Syntax

import Compiler.MAlonzo.Misc
import Compiler.MAlonzo.Pretty
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import Utils.Monad

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
  [ "NATURAL" |-> decls ["ZERO", "SUC"]
      mazNatToInteger "let { f <<0>>     = 0 :: Integer;\
                      \      f (<<1>> x) = 1 + f (unsafeCoerce x);\
                      \} in f"
      mazIntegerToNat "let { f x | x <= (0 :: Integer) = <<0>>\
                      \          | True = <<1>> (unsafeCoerce (f (x - 1)))\
                      \} in f"
  , "LIST"   |-> forList
  , "STRING" |-> forList
  , "BOOL"   |-> decls ["TRUE", "FALSE"]
       mazBoolToHBool "let { f <<0>> = True; f <<1>> = False; } in f"
       mazHBoolToBool "let { f True = <<0>>; f False = <<1>>; } in f"
  , "CHAR"   |-> return [fakeDS mazCharToInteger
                 "(fromIntegral . Data.Char.ord :: Char -> Integer)"]
  ]
  where
    (|->) = (,)
    forList = decls ["NIL", "CONS"]
       mazListToHList "let { f <<0>>        = [];\
                      \      f (<<1>> x xs) = x : f (unsafeCoerce xs)\
                      \} in f"
       mazHListToList "let { f []     = <<0>>;\
                      \      f (c:cs) = <<1>> c (unsafeCoerce (f cs));\
                      \} in f"
    decls cs n1 b1 n2 b2 = do
      cs' <- mapM pconName cs
      return $ zipWith (\ n -> fakeDS n . repl cs') [n1, n2] [b1, b2]
               
mazNatToInteger  = "mazNatToInteger"
mazIntegerToNat  = "mazIntegerToNat"
mazCharToInteger = "mazCharToInteger"
mazListToHList   = "mazListToHList"
mazHListToList   = "mazHListToList"
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
  [ "primNatPlus"   |-> binNat "(+)"
  , "primNatMinus"  |-> binNat "(-)"
  , "primNatTimes"  |-> binNat "(*)"
  , "primCharToNat" |-> do toN <- bltQual' "NATURAL" mazIntegerToNat
                           toI <- bltQual' "CHAR"   mazCharToInteger
                           return $ repl[toN, toI]$ "\\ x -> <<0>> (<<1>> x)"
  , "primCharEquality"   |-> rel "(==)" "Char"
  , "primStringAppend"   |-> binAsis "(++)" "String"
  , "primStringToList"   |-> bltQual' "STRING" mazHListToList
  , "primStringFromList" |-> bltQual' "STRING" mazListToHList
  , "primStringEquality" |-> rel "(==)" "String"
  , "primIntegerPlus"    |-> binAsis "(+)" "Integer"
  , "primIntegerMinus"   |-> binAsis "(-)" "Integer"
  , "primIntegerTimes"   |-> binAsis "(*)" "Integer"
  , "primIntegerDiv"     |-> binAsis "div" "Integer"
  , "primIntegerMod"     |-> binAsis "mod" "Integer"
  , "primIntegerEquality"|-> rel "(==)" "Integer"
  , "primIntegerLess"    |-> rel "(<)"  "Integer"
  , "primIntegerAbs"     |-> do toN <- bltQual' "NATURAL" mazIntegerToNat
                                return $ repl [toN] $ "\\ x -> <<0>> (abs x)"
  , "primNatToInteger"   |-> bltQual' "NATURAL" mazNatToInteger
  , "primPutStr"         |-> return "putStr"
  , "primIOReturn"       |-> return "\\ _ -> (return :: forall a . a -> IO a)"
  , "primIOBind"         |-> return "\\ _ _ -> ((>>=) :: forall a b .\
                                    \ IO a -> (a -> IO b) -> IO b)"
  , "primRound"          |-> return "(round :: Double -> Integer)"
  , "primLog"            |-> return "(log :: Double -> Double)"
  , "primExp"            |-> return "(exp :: Double -> Double)"
  , "primIntegerToFloat" |-> return "(fromIntegral :: Integer -> Double)"
  , "primFloatTimes"     |-> return "((*) :: Double -> Double -> Double)"
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
  rel op ty = do
    toA <- bltQual' "BOOL" mazHBoolToBool
    return $ repl [op, ty, toA] $
      "\\ x y -> <<2>> ((<<0>> :: <<1>> -> <<1>> -> Bool) x y)"
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

bltQual' b s = prettyPrint <$> bltQual b s

