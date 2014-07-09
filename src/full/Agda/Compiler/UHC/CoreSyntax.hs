{-# LANGUAGE CPP #-}

module Agda.Compiler.UHC.CoreSyntax
  ( CoreExpr,
    parseCoreExpr,
    printCoreExpr,
    parseCoreConstr,
    ehcOpts
  )

where


#ifndef UHC_BACKEND

type CoreExpr = ()

parseCoreConstr :: String -> Either String (String, Integer)
parseCoreConstr = undefined

parseCoreCode :: String -> Either String CoreExpr
parseCoreCode = undefined

printCoreExpr :: CoreExpr -> String
printCoreExpr = undefined

#else

import Data.Maybe
import Data.List
import EH99.Opts.Base

import UHC.Util.Pretty

import qualified EH99.Core.Pretty as EP

import EH99.Opts
import EH99.Core
import EH99.AbstractCore
import EH99.Core.Parser
import EH99.Base.Common
import UHC.Util.ParseUtils

import Data.List (intercalate)
import UHC.Util.ScanUtils
import EH99.Scanner.Common
import EH99.Base.HsName

--ehcOpts = emptyEHCOpts { ehcOptCoreOpts = [CoreOpt_Dump] }

type CoreExpr = CExpr

ehcOpts = defaultEHCOpts { ehcOptCoreOpts = [ CoreOpt_Dump ] }

-- TODO very adhoc, do proper parsing instead
parseCoreConstr :: String -> Either String (String, Integer)
parseCoreConstr xs@('(':xss) | last xs == ')' = Right (s1, read $ tail s2)
  where s = init xss
        (s1, s2) = splitAt (fromJust $ elemIndex ',' s) s
parseCoreConstr xs = Left $ "Parse failed: " ++ xs

parseCoreExpr :: String -> Either String CoreExpr
parseCoreExpr str = case errs of
    [] -> Right res
    _  -> Left $ "Parsing core code failed:\n" ++ (intercalate "\n" $ map show errs)
  where scanOpts = coreScanOpts ehcOpts
        tokens = scan scanOpts (initPos str) str
        (res, errs) = parseToResMsgs pCExpr tokens

printCoreExpr :: CoreExpr -> String
printCoreExpr e = disp (pp e) 200 ""
#endif
