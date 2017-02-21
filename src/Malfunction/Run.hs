module Malfunction.Run
  ( compileRunPrint
  , compileModFile
  , runModPrintInts
  , withPrintInts
  , runModFile
  ) where

import           GHC.IO.Handle
import           Malfunction.AST
import           System.IO.Temp
import           System.Process
import System.IO

catMod :: Mod -> Handle -> IO ()
catMod m h = hPutStr h prog >> hFlush h
  where prog = prettyShow m

-- | Compiles an existing file contain malfunction and writes the resulting
-- executable to another file.
compileModFile :: FilePath -> FilePath -> IO ()
compileModFile mlf exe = callProcess "malfunction" ["compile", mlf, "-o", exe]

-- | Writes the module to a temporary files, compiles and executes it.
runMod :: Mod -> IO String
runMod t = withSystemTempFile "term.mlf" $
           \tfp th -> do
             catMod t th
             runModFile' tfp th

-- | Run .mlf
runModFile :: FilePath -> IO String
runModFile tfp = do
  th <- openFile tfp ReadMode
  runModFile' tfp th

runModFile' :: FilePath -> Handle -> IO String
runModFile' mlf th =
  withSystemTempFile "term.x" $
  \xfp xh
  -> do
    compileModFile mlf xfp
    hClose th >> hClose xh
    readProcess xfp [] ""

withPrintInts :: Mod -> [Ident] -> Mod
withPrintInts (MMod bs expo) ids = MMod bs' expo
  where
    bs' = bs ++ map printInt ids
    printInt var = Unnamed $ Mapply (Mglobal ["Pervasives", "print_int"]) [Mvar var]

runModPrintInts :: Mod -> [Ident] -> IO String
runModPrintInts ids = runMod . withPrintInts ids

-- | Compiles an to an executable and executes it.
--
-- Note that this method uses the executable named `agda2mlf` as registered with
-- `stack`.
compileRunPrint :: FilePath -> Ident -> IO String
compileRunPrint agdap var =
  withSystemTempFile "module.mlf" $
    \mlfp mlfh -> do
      callProcess "stack" ["exec", "agda2mlf", "--", "-v0", "--mlf", agdap, "-o", mlfp, "-r", var]
      runModFile' mlfp mlfh
