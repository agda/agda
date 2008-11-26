{-# LANGUAGE RecordPuns, ExistentialQuantification #-}

import Control.Applicative hiding (optional)
import Control.Monad
import System.Directory
import Text.ParserCombinators.ReadP
import Data.Char
import Text.PrettyPrint hiding (char)

instance Applicative ReadP where
  pure = return
  (<*>) = ap

type Bytes = Integer
type MegaBytes = Integer
type Seconds = Float
type Percent = Float
type BytesPerSecond = Bytes

data Statistics = Stats
      { command       :: String
      , allocated
      , copiedScavenged
      , copiedNotScavenged
      , residency     :: Bytes
      , gcGeneration0
      , gcGeneration1 :: (Integer, Seconds)
      , memoryInUse   :: MegaBytes
      , initTime, mutTime
      , gcTime, rpTime
      , profTime, exitTime
      , totalTime     :: Seconds
      , gcPercent     :: Percent
      , allocRate     :: BytesPerSecond
      , productivity  :: Percent
      }
  deriving Show

noStats = Stats "true" 0 0 0 0 (0,0) (0,0) 0 0 0 0 0 0 0 0 0 0 0

lineP :: ReadP String
lineP = do
  s <- munch ('\n' /=)
  char '\n'
  return s

integerP :: ReadP Integer
integerP = do
  skipSpaces
  s <- munch (`elem` (',':['0'..'9']))
  return $ read $ filter (/=',') s

bytesP :: ReadP Bytes
bytesP = integerP <* skipSpaces <* string "bytes"

megaBytesP :: ReadP MegaBytes
megaBytesP = integerP <* skipSpaces <* string "Mb"

floatP :: ReadP Float
floatP = do
  skipSpaces
  s <- munch (`elem` ('.':['0'..'9']))
  return $ read s

timeP :: ReadP Seconds
timeP = floatP <* char 's'

percentP :: ReadP Percent
percentP = floatP <* char '%'

collectionP :: ReadP (Integer, Seconds)
collectionP = do
  n <- integerP
  munch (/= '(')
  char '('
  t <- timeP
  lineP
  return (n, t)

statsP :: ReadP Statistics
statsP = do
  command   <- lineP
  allocated <- bytesP <* lineP
  copiedScavenged <- bytesP <* lineP
  copiedNotScavenged <- bytesP <* lineP
  residency <- bytesP <* lineP
  gcGeneration0 <- collectionP
  gcGeneration1 <- collectionP
  memoryInUse <- megaBytesP <* lineP
  let timeReport s = skipSpaces *> string s *> skipSpaces *> string "time" *> timeP <* lineP
  initTime <- timeReport "INIT"
  mutTime <- timeReport "MUT"
  gcTime <- timeReport "GC"
  rpTime <- option 0 (timeReport "RP")
  profTime <- option 0 (timeReport "PROF")
  exitTime <- timeReport "EXIT"
  totalTime <- timeReport "Total"
  gcPercent <- skipSpaces *> string "%GC time" *> percentP <* lineP
  allocRate <- skipSpaces *> string "Alloc rate" *> bytesP <* lineP
  productivity <- skipSpaces *> string "Productivity" *> percentP <* lineP
  return $ Stats
    { command
    , allocated
    , copiedScavenged
    , copiedNotScavenged
    , residency
    , gcGeneration0
    , gcGeneration1
    , memoryInUse
    , initTime, mutTime
    , gcTime, rpTime
    , profTime, exitTime
    , totalTime
    , gcPercent
    , allocRate
    , productivity
    }

file = "logs/ulf-norells-macbook-pro-20081126-12.59/syntax1"

parseFile file = do
  s <- readFile file
  case readP_to_S statsP s of
    (stats, s'):_ -> return stats
    []            -> error "no parse"

isProperFile ('.':_)  = False
isProperFile "README" = False
isProperFile _        = True

dirContents dir = filter isProperFile <$> getDirectoryContents dir

logDirs :: IO [FilePath]
logDirs = dirContents "logs"

logs :: IO [Log]
logs = map read <$> logDirs

readLogs :: Log -> IO [(FilePath, Statistics)]
readLogs l = do
  let dir = "logs/" ++ logDir l
  xs <- dirContents dir
  mapM (\s -> (,) s <$> parseFile (dir ++ "/" ++ s)) xs

data Log = Log { machine   :: String
               , timeStamp :: String
               }
  deriving (Show)

logDir :: Log -> FilePath
logDir (Log m t) = m ++ "-" ++ t

instance Read Log where
  readsPrec _ = readP_to_S $ do
    m <- many1 get
    char '-'
    d <- count 8 $ satisfy isDigit
    char '-'
    hh <- count 2 $ satisfy isDigit
    char '.'
    mm <- count 2 $ satisfy isDigit
    return $ Log m (d ++ "-" ++ hh ++ "." ++ mm)

data Attr = forall a. Show a => Attr String (Statistics -> a)

stats :: (Log -> Bool) -> (FilePath -> Bool) -> [Attr] -> IO ()
stats goodLog goodCase attrs = do
  ls <- filter goodLog <$> logs
  mapM_ printStat ls
  where
    printStat l = do
      putStrLn $ logDir l
      cs <- filter (goodCase . fst) <$> readLogs l
      print $ vcat $ map prAttrs cs
    prAttrs (c, s) = nest 2 $ text c <+> vcat (map (prAttr s) attrs)
    prAttr s (Attr name f) =
      text name <> text ":" <+> text (show (f s))


