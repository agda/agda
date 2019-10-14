-- Liang-Ting Chen 2019-10-13:
-- this program is partially re-written such that
-- the configuration part is controllfed by an external
-- configuration file `fix-whitespace.yaml"
-- in the base directory instead.

import Control.Monad

import Data.Char as Char
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text  -- Strict IO.

import System.Directory ( getCurrentDirectory )
import System.Environment
import System.Exit
import System.FilePath
import System.FilePath.Find
import System.IO

import ParseConfig

-- The location of the configuration file.
-- TODO: Add an option to specify a custom location.
defaultLoc :: FilePath
defaultLoc = "fix-whitespace.yaml"

-- Modes.

data Mode
  = Fix    -- ^ Fix whitespace issues.
  | Check  -- ^ Check if there are any whitespace issues.
    deriving Eq

main :: IO ()
main = do
  args <- getArgs
  progName <- getProgName
  mode <- case args of
    []          -> return Fix
    ["--check"] -> return Check
    _           -> hPutStr stderr (usage progName) >> exitFailure

  Config incDirs excDirs incFiles excFiles <- parseConfig defaultLoc
  base <- getCurrentDirectory

  changes <- mapM (fix mode) =<<
    find (validDir base incDirs excDirs) (validFile base incFiles excFiles) base

  when (or changes && mode == Check) exitFailure

-- | Usage info.

usage :: String -> String
usage progName = unlines
  [ progName ++ ": Fixes whitespace issues."
  , ""
  , "Usage: " ++ progName ++ " [--check]"
  , ""
  , "This program should be run in the base directory."
  , ""
  , "The program does the following for every file listed in"
  , ""
  , defaultLoc
  , ""
  , "under the current directory:"
  , ""
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

-- Directory filter
validDir
  :: FilePath
     -- ^ The base directory.
  -> [FilePath]
     -- ^ The list of included directories.
  -> [FilePath]
     -- ^ The list of excluded directories if *not* included above.
  -> RecursionPredicate
validDir base incDirs excDirs =
      foldr (||?) never  ((filePath ~~?) . (base </>) <$> incDirs)
  ||? foldr (&&?) always ((filePath /~?) . (base </>) <$> excDirs)

-- File filter
validFile
  :: FilePath
     -- ^ The base directory.
  -> [FilePath]
     -- ^ The list of files to check.
  -> [FilePath]
     -- ^  The list of excluded file names if included above.
  -> FindClause Bool
validFile base incFiles excFiles =
      foldr (||?) never  ((filePath ~~?) . (base </>) <$> incFiles)
  &&? foldr (&&?) always ((filePath /~?) . (base </>) <$> excFiles)

-- | Unconditionally return False.
never :: FindClause Bool
never = return False

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
      hPutStrLn stderr $
        "Whitespace violation " ++
        (if mode == Fix then "fixed" else "detected") ++
        " in " ++ f ++ "."
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
  map (removeTrailingWhitespace .  convertTabs) .
  Text.lines
  where
  removeFinalEmptyLinesExceptOne =
    reverse . dropWhile1 Text.null . reverse

  removeTrailingWhitespace =
    Text.dropWhileEnd ((`elem` [Space,Format]) . generalCategory)

  convertTabs =
    Text.pack . reverse . fst . foldl convertOne ([], 0) . Text.unpack

  convertOne (a, p) '\t' = (addSpaces n a, p + n)
                           where
                             n = 8 - p `mod` 8
  convertOne (a, p) c = (c:a, p+1)

  addSpaces 0 x = x
  addSpaces n x = addSpaces (n-1) (' ':x)

-- | 'dropWhile' except keep the first of the dropped elements
dropWhile1 :: (a -> Bool) -> [a] -> [a]
dropWhile1 _ [] = []
dropWhile1 p (x:xs)
  | p x       = x : dropWhile p xs
  | otherwise = x : xs
