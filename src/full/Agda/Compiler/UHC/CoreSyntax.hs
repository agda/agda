{-# LANGUAGE CPP #-}

module Agda.Compiler.UHC.CoreSyntax
  ( CoreExpr,
    parseCoreExpr,
    printCoreExpr,
    ehcOpts
  )

where


#ifndef UHC_BACKEND

type CoreExpr = ()

parseCoreCode :: String -> Either String CoreExpr
parseCoreCode = undefined

printCoreExpr :: CoreExpr -> String
printCoreExpr = undefined

#else

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
