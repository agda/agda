{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NamedFieldPuns #-}

import Control.Applicative hiding (optional, many)
import Control.Monad
import System.Directory
import Text.ParserCombinators.ReadP
import Data.Char
import Data.List
import Text.PrettyPrint hiding (char)
import Text.Printf
import Data.Monoid
import System.Environment

type Bytes = Integer
type MegaBytes = Integer
type Seconds = Float
type Percent = Float
type BytesPerSecond = Bytes
type Metas = Integer

data Statistics = Stats
      { command              :: String
      , memoryInUse          :: MegaBytes
      , totalTime            :: Seconds
      , numberOfMetas        :: Metas
      , attemptedConstraints :: Integer
      , maxMetas             :: Integer
      , maxConstraints       :: Integer
      }

instance Show Statistics where
  show (Stats _ mem time meta cs maxMeta maxCs) =
    printf "%6.2fs - %4dMB - %5d (%3d) metas - %5d (%3d) constraints" time mem meta maxMeta cs maxCs

noStats = Stats "true" 0 0

notP :: ReadP a -> ReadP ()
notP p = do
  s <- look
  case readP_to_S p s of
    []  -> return ()
    _   -> pfail

-- Greedy version of many
many' :: ReadP a -> ReadP [a]
many' p = many p <* notP p

orElse :: ReadP a -> ReadP a -> ReadP a
orElse p q = p +++ (notP p *> q)

munchTo :: Char -> ReadP String
munchTo c = munch (c /=) <* char c

lineP :: ReadP String
lineP = munchTo '\n'

integerP :: ReadP Integer
integerP = do
  skipSpaces
  s <- filter (/=',') <$> munch1 (`elem` (',':['0'..'9']))
  guard (not $ null s)
  return $ read s

bytesP :: ReadP Bytes
bytesP = integerP <* skipSpaces <* string "bytes"

megaBytesP :: ReadP MegaBytes
megaBytesP = integerP <* skipSpaces <* (string "Mb" +++ string "MB" +++ string "MiB")

floatP :: ReadP Float
floatP = do
  skipSpaces
  s <- munch1 (`elem` ('.':['0'..'9']))
  return $ read s

timeP :: ReadP Seconds
timeP = floatP <* char 's'

percentP :: ReadP Percent
percentP = floatP <* char '%'

metaP :: ReadP Metas
metaP = munchTo ':' *> integerP <* string " metas" <* lineP

collectionP :: ReadP (Integer, Seconds)
collectionP = (,) <$> integerP <* munchTo '(' <*> timeP <* lineP

data Ticks = Tick String Integer
  deriving (Show)

tickP = Tick <$> label <*> integerP <* lineP
  where
    label = unwords <$> many (munch (== ' ') *> munch1 (not . isSpace))

ticksP =
  string "Accumulated statistics" *> lineP *> many' tickP

statsP :: ReadP Statistics
statsP = do
  ticks <- ticksP `orElse` return []
  let numberOfMetas        = sum [ n | Tick "metas" n <- ticks ]
      attemptedConstraints = sum [ n | Tick "attempted-constraints" n <- ticks ]
      maxMetas             = maximum $ 0 : [ n | Tick "max-open-metas" n <- ticks ]
      maxConstraints       = maximum $ 0 : [ n | Tick "max-open-constraints" n <- ticks ]
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
    , numberOfMetas
    , attemptedConstraints
    , maxMetas
    , maxConstraints
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
      let w = maximum $ 0 : [ length name | (name, _) <- cs ]
      print $ vcat $ map (prAttrs w) cs
    prAttrs w (c, s) = nest 2 $ text (pad c) <+> vcat (map (prAttr s) attrs)
      where
        pad s = s ++ replicate (w - length s) ' ' ++ ":"
    prAttr s (Attr name f) = text (show (f s))

time = stats (const True) (const True) [Attr "time" totalTime]
mem  = stats (const True) (const True) [Attr "space" memoryInUse]

summary = stats (const True) (const True) [Attr "stats" id]

main = do
  args <- getArgs
  case args of
    []  -> summary
    [l] -> stats ((l `isInfixOf`) . logDir) (const True) [Attr "stats" id]
    _   -> do
      prog <- getProgName
      putStrLn $ "Usage: " ++ prog ++ " [LOG]"

