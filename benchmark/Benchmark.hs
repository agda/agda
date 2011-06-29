{-# LANGUAGE NamedFieldPuns, ExistentialQuantification #-}

import Control.Applicative hiding (optional, many)
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
      , memoryInUse   :: MegaBytes
      , totalTime     :: Seconds
      }
  deriving Show

noStats = Stats "true" 0 0

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
megaBytesP = integerP <* skipSpaces <* (string "Mb" +++ string "MB")

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
  command <- lineP
  many lineP
  memoryInUse <- skipSpaces *> megaBytesP <* skipSpaces <* string "total memory" <* lineP
  let timeReport s = skipSpaces *> string s *> skipSpaces *> string "time" *> timeP <* lineP
  many lineP
  totalTime <- timeReport "Total"
  many lineP
  return $ Stats
    { command
    , memoryInUse
    , totalTime
    }

file = "logs/ulf-norells-macbook-pro-20081126-12.59/syntax1"

runReadP p s =
  case readP_to_S p s of
    (x, _):_ -> x
    []       -> error $ "no parse:\n" ++ s

parseFile file = do
  s <- readFile file
  case readP_to_S statsP s of
    (stats, s'):_ -> return stats
    []            -> error $ "no parse: " ++ file ++ "\n" ++ s

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
logDir (Log m t) = t ++ "-" ++ m

instance Read Log where
  readsPrec _ = readP_to_S $ do
    d <- count 8 $ satisfy isDigit
    char '-'
    hh <- count 2 $ satisfy isDigit
    char '.'
    mm <- count 2 $ satisfy isDigit
    char '-'
    m <- many1 get
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

time = stats (const True) (const True) [Attr "time" totalTime]
mem  = stats (const True) (const True) [Attr "space" memoryInUse]

