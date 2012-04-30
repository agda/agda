import Control.Monad
import Data.Char as Char
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text  -- Strict IO.
import System.Environment
import System.Exit
import System.FilePath.Find
import System.IO

-- Configuration parameters.

extensions = [".hs", ".hs-boot", ".x", ".y", ".el"]
srcDir     = "src"

-- Modes.

data Mode
  = Fix    -- ^ Fix whitespace issues.
  | Check  -- ^ Check if there are any whitespace issues.
    deriving Eq

main = do
  args <- getArgs
  mode <- case args of
    []          -> return Fix
    ["--check"] -> return Check
    _           -> hPutStr stderr usage >> exitFailure

  changes <-
    mapM (fix mode) =<<
      find always (foldr1 (||?) $ map (extension ==?) extensions) srcDir

  when (or changes && mode == Check) exitFailure

-- | Usage info.

usage :: String
usage = unlines
  [ "fix-agda-whitespace: Fixes whitespace issues for Agda sources."
  , ""
  , "Usage: fix-agda-whitespace [--check]"
  , ""
  , "This program should be run in the base directory."
  , ""
  , "By default the program does the following for every"
  , list extensions ++ " file under " ++ srcDir ++ ":"
  , "* Removes trailing whitespace."
  , "* Removes trailing lines containing nothing but whitespace."
  , "* Ensures that the file ends in a newline character."
  , ""
  , "With the --check flag the program does not change any files,"
  , "it just checks if any files would have been changed. In this"
  , "case it returns with a non-zero exit code."
  , ""
  , "Background: Agda was reported to fail to compile on Windows"
  , "because a file did not end with a newline character (Agda"
  , "uses -Werror)."
  ]
  where
  list [x]      = x
  list [x, y]   = x ++ " and " ++ y
  list (x : xs) = x ++ ", " ++ list xs

-- | Fix a file. Only performs changes if the mode is 'Fix'. Returns
-- 'True' iff any changes would have been performed in the 'Fix' mode.

fix :: Mode -> FilePath -> IO Bool
fix mode f = do
  new <- withFile f ReadMode $ \h -> do
    hSetEncoding h utf8
    s <- Text.hGetContents h
    let s' = transform s
    return $ if s' == s then Nothing else Just s'
  case new of
    Nothing -> return False
    Just s  -> do
      putStrLn $ "Whitespace violation " ++ (if mode == Fix then "fixed" else "detected") ++ " in " ++ f
      when (mode == Fix) $
        withFile f WriteMode $ \h -> do
          hSetEncoding h utf8
          Text.hPutStr h s
      return True

-- | Transforms the contents of a file.

transform :: Text -> Text
transform =
  Text.unlines .
  removeFinalEmptyLinesExceptOne .
  map removeTrailingWhitespace .
  Text.lines
  where
  removeFinalEmptyLinesExceptOne =
    reverse . dropWhile1 Text.null . reverse

  removeTrailingWhitespace =
    Text.dropWhileEnd Char.isSpace

-- | 'dropWhile' except keep the first of the dropped elements
dropWhile1 p [] = []
dropWhile1 p (x:xs)
  | p x       = x : dropWhile p xs
  | otherwise = x : xs
