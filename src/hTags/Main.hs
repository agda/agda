{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Trans
import Data.Char
import Data.List
import Data.Maybe
import System.Environment
import System.IO
import qualified System.IO.Strict as Strict
import System.Exit
import System.FilePath
import System.Directory
import System.Process
import System.Console.GetOpt

import GHC
import Parser as P
import Lexer
import DriverPipeline
import FastString
import DriverPhases
import ErrUtils
import StringBuffer
import SrcLoc
import Outputable
import DynFlags (opt_P, sOpt_P)
import GhcMonad (GhcT(..), Ghc(..))

import Tags

instance MonadTrans GhcT where
  lift m = GhcT $ const m

fileLoc :: FilePath -> RealSrcLoc
fileLoc file = mkRealSrcLoc (mkFastString file) 1 0

filePState :: DynFlags -> FilePath -> IO PState
filePState dflags file = do
  buf <- hGetStringBuffer file
  return $
    mkPState dflags buf (fileLoc file)

pMod :: P (Located (HsModule RdrName))
pMod = P.parseModule

parse :: PState -> P a -> ParseResult a
parse st p = Lexer.unP p st

goFile :: FilePath -> Ghc [Tag]
goFile file = do
  liftIO $ hPutStrLn stderr $ "Processing " ++ file
  env <- getSession
  (dflags, srcFile) <- liftIO $
      preprocess env (file, Just $ Cpp HsSrcFile)
  st <- liftIO $ filePState dflags srcFile
  case parse st pMod of
    POk _ m         -> return $ removeDuplicates $ tags $ unLoc m
    PFailed loc err -> liftIO $ do
      print (mkPlainErrMsg dflags loc err)
      exitWith $ ExitFailure 1

runCmd :: String -> IO String
runCmd cmd = do
  (_, h, _, _) <- runInteractiveCommand cmd
  hGetContents h

main :: IO ()
main = do
  opts <- getOptions
  let go | optHelp opts = do
            printUsage stdout
            exitSuccess
         | otherwise = do
            top : _ <- lines <$> runCmd "ghc --print-libdir"
            ts <- runGhc (Just top) $ do
              dynFlags <- getSessionDynFlags
              setSessionDynFlags $
                dynFlags {
                  settings = (settings dynFlags) {
                    sOpt_P = concatMap (\i -> [i, "-include"]) (optIncludes opts) ++
                             opt_P dynFlags
                    },
                  includePaths = optIncludePath opts ++ includePaths dynFlags
                  }
              mapM (\f -> liftM2 ((,,) f) (liftIO $ Strict.readFile f)
                                          (goFile f)) $
                         optFiles opts
            when (optCTags opts) $
              let sts = sort $ concatMap (\(_, _, t) -> t) ts in
              writeFile (optCTagsFile opts) $ unlines $ map show sts
            when (optETags opts) $
              writeFile (optETagsFile opts) $ showETags ts
  go

getOptions :: IO Options
getOptions = do
  args <- getArgs
  case getOpt Permute options args of
    ([], [], []) -> do
      printUsage stdout
      exitSuccess
    (opts, files, []) -> return $ foldr ($) (defaultOptions files) opts
    (_, _, errs) -> do
      hPutStr stderr $ unlines errs
      printUsage stderr
      exitWith $ ExitFailure 1

printUsage h = do
  prog <- getProgName
  hPutStrLn h $ usageInfo prog options

data Options = Options
  { optCTags       :: Bool
  , optETags       :: Bool
  , optCTagsFile   :: String
  , optETagsFile   :: String
  , optHelp        :: Bool
  , optIncludes    :: [FilePath]
  , optFiles       :: [FilePath]
  , optIncludePath :: [FilePath]
  }

defaultOptions :: [FilePath] -> Options
defaultOptions files = Options
  { optCTags       = False
  , optETags       = False
  , optCTagsFile   = "tags"
  , optETagsFile   = "TAGS"
  , optHelp        = False
  , optIncludes    = []
  , optFiles       = files
  , optIncludePath = []
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option []    ["help"]    (NoArg setHelp)  "Show help."
  , Option ['c'] ["ctags"]   (OptArg setCTagsFile "FILE") "Generate ctags (default file=tags)"
  , Option ['e'] ["etags"]   (OptArg setETagsFile "FILE") "Generate etags (default file=TAGS)"
  , Option ['i'] ["include"] (ReqArg addInclude   "FILE") "File to #include"
  , Option ['I'] []          (ReqArg addIncludePath "DIRECTORY") "Directory in the include path"
  ]
  where
    setHelp             o = o { optHelp        = True }
    setCTags            o = o { optCTags       = True }
    setETags            o = o { optETags       = True }
    setCTagsFile   file o = o { optCTagsFile   = fromMaybe "tags" file, optCTags = True }
    setETagsFile   file o = o { optETagsFile   = fromMaybe "TAGS" file, optETags = True }
    addInclude     file o = o { optIncludes    = file : optIncludes o }
    addIncludePath dir  o = o { optIncludePath = dir : optIncludePath o}
