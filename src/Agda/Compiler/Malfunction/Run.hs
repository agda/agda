module Agda.Compiler.Malfunction.Run
  ( compileRunPrint
  , compileModFile
  , runModPrintInts
  , withPrintInts
  , runModFile
  , runMalfunction
  ) where

import           GHC.IO.Handle
import           System.FilePath
import           System.IO
import           System.IO.Temp
import           System.Process

import           Agda.Compiler.Malfunction.AST

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
      callProcess "stack" ["exec", "agda2mlf", "--", "-v0", "--mlf", agdap
                          , "-o", mlfp, "--print-var", var]
      runModFile' mlfp mlfh

-- FIXME: I do almost the same as existing functions in this module.
--
-- I do realize that similar functionality exists in `Malfunction.Run` I didn't
-- use this because it also prints some stuff to stdout, so I felt it was easier
-- to just repeat these 3 lines of code.
--
-- | `runMalfunction fp inp` calls the malfunction compiler on the input `inp`
-- and places the output at `fp`. Assumes that the executable `malfunction` is
-- in `PATH`.
runMalfunction :: FilePath -> String -> IO ()
runMalfunction nm modl = takeBaseName nm `withSystemTempFile` \fp h -> do
  hPutStr h modl
  hFlush h
  callProcess "malfunction" ["compile", fp, "-o", nm]
