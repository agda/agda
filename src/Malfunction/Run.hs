module Malfunction.Run where

import           GHC.IO.Handle
import           Malfunction.AST
import           System.IO.Temp
import           System.Process
import System.IO

catMod :: Mod -> Handle -> IO ()
catMod m h = hPutStr h prog >> hFlush h
  where prog = prettyShow m

compileModFile :: FilePath -> FilePath -> IO ()
compileModFile mlf exe = callProcess "malfunction" ["compile", mlf, "-o", exe]

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

compileRunPrint :: FilePath -> Ident -> IO String
compileRunPrint agdap var = do
  withSystemTempFile "module.mlf" $
    \mlfp mlfh -> do
      callProcess "stack" ["exec", "agda2mlf", "--", "--mlf", agdap, "-o", mlfp, "-r", var]
      runModFile' mlfp mlfh

-- Example:
--   (module
--     (_ (apply (global $Pervasives $print_string) "Hello, world!\n"))
--     (export))
helloMod :: Mod
helloMod = MMod [Unnamed helloT] []
  where
    helloT = Mapply (Mglobal ["Pervasives", "print_string"])
                 [Mstring "Hello, world!\n"]

