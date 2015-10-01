
module Agda.Interaction.Library
  ( getDefaultLibraries
  , getInstalledLibraries
  , libraryIncludePaths
  ) where

import Control.Arrow (first, second)
import Control.Applicative
import Control.Exception
import Control.Monad.Writer
import Control.Monad.Except
import Data.Char
import Data.Either
import Data.List
import System.Directory
import System.FilePath

import Agda.Interaction.Library.Base
import Agda.Interaction.Library.Parse
import Agda.Utils.Monad
import Agda.Utils.Environment

type LibM = ExceptT String IO

catchIO :: IO a -> (IOException -> IO a) -> IO a
catchIO = catch

getAgdaAppDir :: IO FilePath
getAgdaAppDir = getAppUserDataDirectory "agda"

libraryFile :: FilePath
libraryFile = "libraries"

defaultsFile :: FilePath
defaultsFile = "defaults"

data LibError = LibNotFound LibName
              | AmbiguousLib LibName [AgdaLibFile]
              | OtherError String
  deriving (Show)

mkLibM :: [AgdaLibFile] -> IO (a, [LibError]) -> LibM a
mkLibM libs m = do
  (x, err) <- lift m
  case err of
    [] -> return x
    _  -> throwError =<< lift (unlines <$> mapM (formatLibError libs) err)

getDefaultLibraries :: LibM [LibName]
getDefaultLibraries = mkLibM [] $ do
  libs <- filter ((== ".agda-lib") . takeExtension) <$> getDirectoryContents "."
  if null libs then readDefaultsFile
    else first (map libName) <$> parseLibFiles libs

readDefaultsFile :: IO ([LibName], [LibError])
readDefaultsFile = do
    agdaDir <- getAgdaAppDir
    let file = agdaDir </> defaultsFile
    ifM (doesFileExist file) (do
      ls <- stripCommentLines <$> readFile file
      return ("." : concatMap splitCommas ls, [])
      ) {- else -} (return (["."], []))
  `catchIO` \e -> return (["."], [OtherError $ "Failed to read defaults file.\n" ++ show e])

getInstalledLibraries :: LibM [AgdaLibFile]
getInstalledLibraries = mkLibM [] $ do
    agdaDir <- getAgdaAppDir
    let file = agdaDir </> libraryFile
    ifM (doesFileExist file) (do
      files <- mapM expandEnvironmentVariables =<< stripCommentLines <$> readFile file
      parseLibFiles files
      ) {- else -} (return ([], []))
  `catchIO` \e -> return ([], [OtherError $ "Failed to read installed libraries.\n" ++ show e])

parseLibFiles :: [FilePath] -> IO ([AgdaLibFile], [LibError])
parseLibFiles files = do
  rs <- mapM parseLibFile files
  let errs = [ OtherError $ path ++ ":" ++ (if all isDigit (take 1 err) then "" else " ") ++ err
             | (path, Left err) <- zip files rs ]
  return (rights rs, errs)

stripCommentLines :: String -> [String]
stripCommentLines = concatMap strip . lines
  where
    strip s = [ s' | not $ null s' ]
      where s' = stripComments $ dropWhile isSpace s

formatLibError :: [AgdaLibFile] -> LibError -> IO String
formatLibError installed (LibNotFound lib) = do
  agdaDir <- getAgdaAppDir
  return $ "Library '" ++ lib ++ "' not found. " ++
           " Add the path to its .agda-lib file to " ++ (agdaDir </> libraryFile) ++ " to install.\n" ++
           unlines ("Installed libraries:" :
                    if null installed then ["  (none)"]
                    else [ "  " ++ libName l ++ " (" ++ libFile l ++ ")" | l <- installed ])
formatLibError _ (AmbiguousLib lib tgts) = return $
  "Ambiguous library '" ++ lib ++ "'. Could refer to any one of\n" ++
  init (unlines [ "  " ++ libName l ++ " (" ++ libFile l ++ ")" | l <- tgts ])
formatLibError _ (OtherError err) = return err

libraryIncludePaths :: [AgdaLibFile] -> [LibName] -> LibM [FilePath]
libraryIncludePaths libs xs0 = mkLibM libs $ return $ runWriter ((dot ++) . incs <$> find [] xs)
  where
    xs = map trim $ delete "." xs0
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
    incs = nub . concatMap libIncludes
    dot = [ "." | elem "." xs0 ]

    findLib x = [ (m, l) | l <- libs, let m = matchLib x l, m /= NoMatch ]

    find :: [LibName] -> [LibName] -> Writer [LibError] [AgdaLibFile]
    find _ [] = pure []
    find visited (x : xs)
      | elem x visited = find visited xs
      | otherwise =
          case findLib x of
            [(Exact, l)] -> (l :) <$> find (x : visited) (libDepends l ++ xs)
            []           -> tell [LibNotFound x] >> find (x : visited) xs
            ls           -> tell [AmbiguousLib x (map snd ls)] >> find (x : visited) xs

data MatchedName = Exact | NoMatch
  deriving (Eq, Show)

matchLib :: LibName -> AgdaLibFile -> MatchedName
matchLib x l | x == libName l = Exact
matchLib _ _ = NoMatch

