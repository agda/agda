import Control.Monad

import Data.Char as Char
import Data.Functor
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text  -- Strict IO.

import System.Directory ( getCurrentDirectory )
import System.Environment
import System.Exit
import System.FilePath
import System.FilePath.Find
import System.IO

-- Configuration parameters.

extensions :: [String]
extensions =
  [ ".agda"
  , ".cabal"
  , ".el"
  , ".hs"
  , ".hs-boot"
  , ".lagda"
  , ".lhs"
  , ".md"
  , ".rst"
  , ".x"
  , ".y"
  , ".yaml"
  , ".yml"
  ]

-- In test/succeed/LineEndings/ we test that Agda can handle various
-- kinds of whitespace, so we exclude this directory.
validDir
  :: FilePath
     -- ^ The base directory.
  -> RecursionPredicate
validDir base =
 filePath ==? (base </> "src/full/Agda/Compiler/MAlonzo")
   ||?
 foldr1 (&&?)
   ([ fileName /~? "dist*"
    , fileName /=? "MAlonzo"
    ]
      ++
    map (\d -> filePath /=? base </> d)
        [ "_darcs", ".git", "std-lib", "test/bugs"
        , "test/Succeed/LineEndings"
        , "examples/uptodate"
        ])

-- Andreas (24 Sep 2014).
-- | The following files are exempt from the whitespace check,
--   as they test behavior of Agda with regard to tab characters.
excludedFiles :: [FilePath]
excludedFiles =
  [ "Whitespace.agda"                       -- in test/succeed
  , "Issue1337.agda"                        -- in test/succeed
  , "Tabs.agda"                             -- in test/fail
  , "TabsInPragmas.agda"                    -- in test/fail
  , "Lexer.hs"                              -- could be in src/full/Agda/Syntax/Parser
  , "AccidentalSpacesAfterBeginCode.lagda"  -- in test/LaTeXAndHTML/succeed
  ]

-- Auxiliary functions.

filesFilter :: FindClause Bool
filesFilter = foldr1 (||?) (map (extension ==?) extensions)
          &&? foldr1 (&&?) (map (fileName /=?) excludedFiles)

-- Modes.

data Mode
  = Fix    -- ^ Fix whitespace issues.
  | Check  -- ^ Check if there are any whitespace issues.
    deriving Eq

main :: IO ()
main = do
  args <- getArgs
  mode <- case args of
    []          -> return Fix
    ["--check"] -> return Check
    _           -> hPutStr stderr usage >> exitFailure

  base <- getCurrentDirectory
  changes <- mapM (fix mode) =<< find (validDir base) filesFilter base

  when (or changes && mode == Check) exitFailure

-- | Usage info.

usage :: String
usage = unlines
  [ "fix-agda-whitespace: Fixes whitespace issues."
  , ""
  , "Usage: fix-agda-whitespace [--check]"
  , ""
  , "This program should be run in the base directory."
  , ""
  , "By default the program does the following for every"
  , list extensions ++ " file under the current directory:"
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
