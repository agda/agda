module RunTests where

import Control.Monad
import Data.List
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.Process

------------------------------------------------------------------------

latexDir   = "latex"
succeedDir = "succeed"

main :: IO ()
main = do

  args <- getArgs

  case args of
    ["runTests"] -> runTests
    ["clean"]    -> clean
    _            -> do
      putStrLn "Wrong argument."
      exitFailure

------------------------------------------------------------------------

runTests :: IO ()
runTests = do

  dir   <- getCurrentDirectory
  files <- getDirectoryContents $ dir </> succeedDir

  let lagdas = sort $ filter (".lagda" `isSuffixOf`) files
  let texs   = sort $ filter (".tex"   `isSuffixOf`) files

  when (length lagdas /= length texs) $ do

    putStrLn "Not as many .lagda files as .tex files."
    exitFailure

  forM_ (zip lagdas texs) $ \(lagda, tex) -> do

    setCurrentDirectory $ dir </> succeedDir
    rawSystem "agda" ["--latex", lagda]
    exit <- rawSystem "diff" [ "-u", latexDir </> tex, tex ]

    when (isFailure exit) $ do
      putStrLn ""
      putStrLn $ "Output of " ++ lagda ++ " is wrong!"
      exitFailure

    -- If a .compile exists in, then run pdflatex on the produced .tex
    -- file and make sure it succeeds compiling it.
    let pdf = replaceExtension lagda "compile"
    exists <- doesFileExist pdf

    when exists $ do
      setCurrentDirectory latexDir
      exit <- rawSystem "pdflatex" [ "-interaction=batchmode" , tex ]

      when (isFailure exit) $ do
        putStrLn ""
        putStrLn $ tex ++ " doesn't compile!"
        exitFailure

  putStrLn "All tests passed."

isFailure :: ExitCode -> Bool
isFailure (ExitFailure _) = True
isFailure _               = False

------------------------------------------------------------------------

clean :: IO ()
clean = do

  dir <- getCurrentDirectory

  -- Remove latex directory.
  removeDirectoryRecursive $ dir </> succeedDir </> latexDir

  -- Remove interface files.
  files <- getDirectoryContents $ dir </> succeedDir
  let agdais = filter (".agdai" `isSuffixOf`) files
  forM_ agdais $ \agdai ->
    removeFile $ succeedDir </> agdai
