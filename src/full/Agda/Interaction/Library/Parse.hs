module Agda.Interaction.Library.Parse (parseLibFile, stripComments, splitCommas) where

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Char
import qualified Data.List as List
import System.FilePath

import Agda.Interaction.Library.Base
import Agda.Utils.Except ( MonadError(throwError) )

catchIO :: IO a -> (IOException -> IO a) -> IO a
catchIO = catch

type P = Either String

type GenericFile = [(String, [String])]

data Field = forall a. Field
  { fName     :: String
  , fOptional :: Bool
  , fParse    :: [String] -> P a
  , fSet      :: a -> AgdaLibFile -> AgdaLibFile }

-- | .agda-lib file format
agdaLibFields :: [Field]
agdaLibFields =
  [ Field "name"    False parseName                      $ \ name l -> l { libName     = name }
  , Field "include" True  (pure . concatMap words)       $ \ inc  l -> l { libIncludes = inc }
  , Field "depend"  True  (pure . concatMap splitCommas) $ \ ds   l -> l { libDepends  = ds }
  ]
  where
    parseName [s] | [name] <- words s = pure name
    parseName ls = throwError $ "Bad library name: '" ++ unwords ls ++ "'"

defaultLibFile :: AgdaLibFile
defaultLibFile = AgdaLib { libName = "", libFile = "", libIncludes = [], libDepends = [] }

-- | .agda-lib parser
parseLibFile :: FilePath -> IO (P AgdaLibFile)
parseLibFile file =
  (fmap setPath . parseLib <$> readFile file) `catchIO` \e ->
    return (Left $ "Failed to read library file " ++ file ++ ".\nReason: " ++ show e)
  where
    setPath lib = unrelativise (takeDirectory file) lib{ libFile = file }
    unrelativise dir lib = lib { libIncludes = map (dir </>) (libIncludes lib) }

parseLib :: String -> P AgdaLibFile
parseLib s = fromGeneric =<< parseGeneric s

findField :: String -> [Field] -> P Field
findField s fs =
  case [ f | f <- fs, fName f == s ] of
    f : _ -> return f
    []    -> throwError $ "Unknown field '" ++ s ++ "'"

fromGeneric :: GenericFile -> P AgdaLibFile
fromGeneric = fromGeneric' agdaLibFields

fromGeneric' :: [Field] -> GenericFile -> P AgdaLibFile
fromGeneric' fields fs = do
  checkFields fields (map fst fs)
  foldM upd defaultLibFile fs
  where
    upd :: AgdaLibFile -> (String, [String]) -> P AgdaLibFile
    upd l (h, cs) = do
      Field{..} <- findField h fields
      x         <- fParse cs
      return $ fSet x l

checkFields :: [Field] -> [String] -> P ()
checkFields fields fs = do
  let mandatory = [ fName f | f <- fields, not $ fOptional f ]
      missing   = mandatory List.\\ fs
      dup       = fs List.\\ List.nub fs
      s xs      = if length xs > 1 then "s" else ""
      list xs   = List.intercalate ", " [ "'" ++ f ++ "'" | f <- xs ]
  when (not $ null missing) $ throwError $ "Missing field" ++ s missing ++ " " ++ list missing
  when (not $ null dup)     $ throwError $ "Duplicate field" ++ s dup ++ " " ++ list dup

-- Generic file parser ----------------------------------------------------

parseGeneric :: String -> P GenericFile
parseGeneric s =
  groupLines =<< concat <$> mapM (uncurry parseLine) (zip [1..] $ map stripComments $ lines s)

data GenericLine = Header Int String | Content Int String
  deriving (Show)

parseLine :: Int -> String -> P [GenericLine]
parseLine _ "" = pure []
parseLine l s@(c:_)
  | isSpace c   = pure [Content l $ trim s]
  | otherwise   =
    case break (==':') s of
      (h, ':' : r) ->
        case words h of
          [h] -> pure $ [Header l h] ++ [Content l s | let s = trim r, not (null s)]
          []  -> throwError $ show l ++ ": Missing field name"
          hs  -> throwError $ show l ++ ": Bad field name " ++ show h
      _ -> throwError $ show l ++ ": Missing ':' for field " ++ show (trim s)

groupLines :: [GenericLine] -> P GenericFile
groupLines [] = pure []
groupLines (Content l c : _) = throwError $ show l ++ ": Missing field"
groupLines (Header _ h : ls) = ((h, [ c | Content _ c <- cs ]) :) <$> groupLines ls1
  where
    (cs, ls1) = span isContent ls
    isContent Content{} = True
    isContent Header{} = False

trim :: String -> String
trim = stripComments . dropWhile isSpace

splitCommas :: String -> [String]
splitCommas s = words $ map (\c -> if c == ',' then ' ' else c) s

-- | ...and trailing, but not leading, whitespace.
stripComments :: String -> String
stripComments "" = ""
stripComments ('-':'-':_) = ""
stripComments (c : s)     = cons c (stripComments s)
  where
    cons c "" | isSpace c = ""
    cons c s = c : s
