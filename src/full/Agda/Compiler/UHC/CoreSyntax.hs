{-# LANGUAGE CPP #-}
-- | Defines UHC Core functions used in other parts of Agda.
-- E.g. parsing Core pragmas uses the `parseCoreCode` function.
module Agda.Compiler.UHC.CoreSyntax
  ( CoreExpr,
    parseCoreExpr,
    printCoreExpr,
    parseCoreConstr,
    HsName
  )

where



#ifdef UHC_BACKEND

import Data.Maybe
import Data.List
import Data.List (intercalate)



import UHC.Light.Compiler.Core.API as CA

import UHC.Util.ParseUtils
import UHC.Util.Pretty
import UHC.Util.ScanUtils
import UU.Scanner.Position

#endif


#ifndef UHC_BACKEND

type CoreExpr = ()

parseCoreConstr :: String -> Either String (String, Integer)
parseCoreConstr = undefined

parseCoreCode :: String -> Either String CoreExpr
parseCoreCode = undefined

printCoreExpr :: CoreExpr -> String
printCoreExpr = undefined

#else

type CoreExpr = CExpr


-- TODO should work with just the defaultEHCOpts, I guess?
--ehcOpts :: EHCOpts
--ehcOpts = defaultEHCOpts { ehcOptCoreOpts = [ CoreOpt_Dump ] }

-- TODO very adhoc, do proper parsing instead
parseCoreConstr :: String   -- ^ datatype name
    -> String   -- ^ Constructor specification (eg. "(Nil,0)").
    -> Either String (HsName, HsName, Int)
parseCoreConstr ty xs@('(':xss) | last xs == ')' = Right (mkHsName1 ty, mkHsName1 s1, read $ tail s2)
  where s = init xss
        (s1, s2) = splitAt (fromJust $ elemIndex ',' s) s
parseCoreConstr _ xs = Left $ "Parse failed: " ++ xs

parseCoreExpr :: String -> Either String CoreExpr
parseCoreExpr str = case CA.parseExpr defaultEHCOpts str of
    (Left errs) -> Left $ "Parsing core code failed:\n" ++ (intercalate "\n" errs)
    (Right res) -> Right res

printCoreExpr :: CoreExpr -> String
printCoreExpr e = disp (pp e) 200 ""
#endif
