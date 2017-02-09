module Malfunction.Run where

import Malfunction.AST
import System.IO.Temp
import GHC.IO.Handle
import System.Process

printMod :: Mod -> Handle -> IO ()
printMod m h = putStrLn prog >> hPutStr h prog >> hFlush h
  where prog = showMod m

compileMod :: Mod -> (FilePath, Handle) -> FilePath -> IO ()
compileMod m (tfp, th) xfp = do
  printMod m th
  callProcess "malfunction" ["compile", tfp, "-o", xfp]

runMod :: Mod -> IO String
runMod t = withSystemTempFile "term.mlf" $ \tfp th
  -> withSystemTempFile "term.x" $ \xfp xh
  -> do
  compileMod t (tfp, th) xfp
  hClose th >> hClose xh
  readProcess xfp [] ""

runModPrintInts :: [Ident] -> Mod -> IO String
runModPrintInts ids (MMod bs expo) = runMod (MMod bs' expo)
  where
    bs' = bs ++ map printInt ids
    printInt var = Unnamed $ Mapply (Mglobal ["Pervasives", "print_int"]) [Mvar var]

-- Example:
--   (module
--     (_ (apply (global $Pervasives $print_string) "Hello, world!\n"))
--     (export))
helloMod :: Mod
helloMod = MMod [Unnamed helloT] []
  where
    helloT = Mapply (Mglobal ["Pervasives", "print_string"])
                 [Mstring "Hello, world!\n"]

