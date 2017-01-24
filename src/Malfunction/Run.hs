module Malfunction.Run where

import Malfunction.AST
import Malfunction.Print
import System.IO.Temp
import GHC.IO.Handle
import System.Process

printTerm :: Term -> Handle -> IO ()
printTerm t h = print prog >> hPutStr h prog >> hFlush h
  where prog = showTermAsProgram t

compileTerm :: Term -> (FilePath, Handle) -> FilePath -> IO ()
compileTerm t (tfp, th) xfp = do
  printTerm t th
  callProcess "malfunction" ["compile", tfp, "-o", xfp]

runTerm :: Term -> IO String
runTerm t = withSystemTempFile "term.mlf" $ \tfp th
  -> withSystemTempFile "term.x" $ \xfp xh
  -> do
  compileTerm t (tfp, th) xfp
  hClose th >> hClose xh
  readProcess xfp [] ""

-- (apply (global $Pervasives $print_string) "Hello, world!\n")
helloWorld :: Term

helloWorld = Mapply (Mglobal ["Pervasives", "print_string"])
                 [Mstring "Hello, world!\n"]
