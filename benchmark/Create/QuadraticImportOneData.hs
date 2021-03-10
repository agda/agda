{-# LANGUAGE LambdaCase #-}

-- | Create a sequence of files each of which imports all previous ones
--   and defines one data type and an alias for its only constructor.
--
-- @
--   module FileNNN where
--
--   import File000
--   ...
--   import File(NNN-1)
--
--   data D : Set where c : D
--
--   test : D
--   test = c
-- @

import Control.Monad      (forM_)
import System.Directory   (createDirectoryIfMissing)
import System.Environment (getArgs, getProgName)
import System.FilePath    ((</>), (<.>))
import Text.Read          (readMaybe)

filePrefix = "File"
mainName   = "Main"

main :: IO ()
main = do
  getArgs >>= \case
    [dir, s] | Just n <- readMaybe s -> run dir n
    _ -> usage

usage :: IO ()
usage = do
  me <- getProgName
  putStr $ unlines
    [ unwords [ "usage:", me, "DIRECTORY", "NUM" ]
    , "Creates in directory DIRECTORY NUM files named " ++ filePrefix ++ "XXX.agda,"
    , "each importing all previous ones, plus a file named " ++ mainName ++ ".agda,"
    , "importing all the other files."
    ]

run
  :: FilePath -- ^ Directory in which to create the files.
  -> Int      -- ^ Number of files to create.
  -> IO ()
run dir n = do
  createDirectoryIfMissing True dir
  -- Create files
  forM_ [0..n-1] $ \ i -> do
    let fileName = (filePrefix ++ print0d w i) <.> "agda"
    writeFile (dir </> fileName) $ createContent n i
  -- Create main file
  writeFile (dir </> "Main" <.> "agda") $ createMainContent n
  where
  w = length $ show n

-- | Created content of main file, importing the others.
createMainContent
  :: Int        -- ^ Number of files we create.
  -> String     -- ^ Content.
createMainContent n = unlines $ concat
  [ map (\ j -> "import " ++ filePrefix ++ print0d w j) [0..n-1]
  ]
  where
  w = length $ show n

-- | Create list of strings containing:
-- @
--   module FileNNN where
--
--   import File000
--   ...
--   import File(NNN-1)
--
--   data D : Set where c : D
--
--   test : D
--   test = c
-- @
createContent
  :: Int        -- ^ Number of files we create.
  -> Int        -- ^ Number of the file we create here.
  -> String     -- ^ Content.
createContent n i = unlines $ concat
  [ [ unwords [ "module" , filePrefix ++ print0d w i, "where" ]
    , ""
    ]
  , map (\ j -> "import " ++ filePrefix ++ print0d w j) [0..i-1]
  , [ ""
    , "data D : Set where c : D"
    , ""
    , "test : D"
    , "test = c"
    ]
  ]
  where
  w = length $ show n

-- | Equivalent to @sprintf("%0<width>d", num)@
print0d
  :: Int      -- ^ Width.
  -> Int      -- ^ Print this integer.
  -> String   -- ^ Padded from the left with 0s.
print0d w i = pad ++ s
  where
  s    = show i
  pad  = replicate (w - length s) '0'
