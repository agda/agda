{-# LANGUAGE CPP, ScopedTypeVariables #-}

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
#if MIN_VERSION_ghc(7,2,1)
import DynFlags (opt_P, sOpt_P)
import GhcMonad (GhcT(..), Ghc(..))
#else
import HscTypes (GhcT(..), Ghc(..))
#endif

import Tags

instance MonadTrans GhcT where
  lift m = GhcT $ \_ -> m

instance MonadIO m => MonadIO (GhcT m) where
  liftIO = lift . liftIO

instance MonadIO Ghc where
  liftIO m = Ghc $ \_ -> m

#if MIN_VERSION_ghc(7,2,1)
fileLoc :: FilePath -> RealSrcLoc
fileLoc file = mkRealSrcLoc (mkZFastString file) 1 0
#else
fileLoc :: FilePath -> SrcLoc
fileLoc file = mkSrcLoc (mkZFastString file) 1 0
#endif

filePState :: DynFlags -> FilePath -> IO PState
filePState dflags file = do
  buf <- hGetStringBuffer file
  return $
#if MIN_VERSION_ghc(7,0,0)
    mkPState dflags buf (fileLoc file)
#else
    mkPState buf (fileLoc file) dflags
#endif

pMod :: P (Located (HsModule RdrName))
pMod = P.parseModule

parse :: PState -> P a -> ParseResult a
parse st p = unP p st

goFile :: FilePath -> Ghc [Tag]
goFile file = do
  env <- getSession
  (dflags, srcFile) <-
#if MIN_VERSION_ghc(7,2,1)
    liftIO $
#endif
      preprocess env (file, Just $ Cpp HsSrcFile)
  st <- liftIO $ filePState dflags srcFile
  case parse st pMod of
    POk _ m         -> return $ removeDuplicates $ tags $ unLoc m
    PFailed loc err -> liftIO $ do
#if MIN_VERSION_ghc(7,6,0)
      print (mkPlainErrMsg dflags loc err)
#else
      printError loc err
#endif
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
            exitWith ExitSuccess
         | otherwise = do
            top : _ <- lines <$> runCmd "ghc --print-libdir"
            ts <- runGhc (Just top) $ do
              dynFlags <- getSessionDynFlags
              setSessionDynFlags $
                dynFlags {
#if MIN_VERSION_ghc(7,2,1)
                  settings = (settings dynFlags) { sOpt_P
#else
                                                   opt_P
#endif
                      = concatMap (\i -> [i, "-include"]) (optIncludes opts) ++
                        opt_P dynFlags
#if MIN_VERSION_ghc(7,2,1)
                    }
#endif
                  }
              mapM (\f -> liftM2 ((,,) f) (liftIO $ readFile f)
                                          (goFile f)) $
                         optFiles opts
            when (optCTags opts) $
              let sts = sort $ concat $ map (\(_, _, t) -> t) ts in
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
      exitWith ExitSuccess
    (opts, files, []) -> return $ foldr ($) (defaultOptions files) opts
    (_, _, errs) -> do
      hPutStr stderr $ unlines errs
      printUsage stderr
      exitWith $ ExitFailure 1

printUsage h = do
  prog <- getProgName
  hPutStrLn h $ usageInfo prog options

data Options = Options
  { optCTags     :: Bool
  , optETags     :: Bool
  , optCTagsFile :: String
  , optETagsFile :: String
  , optHelp      :: Bool
  , optIncludes  :: [FilePath]
  , optFiles     :: [FilePath]
  }

defaultOptions :: [FilePath] -> Options
defaultOptions files = Options
  { optCTags     = False
  , optETags     = False
  , optCTagsFile = "tags"
  , optETagsFile = "TAGS"
  , optHelp      = False
  , optIncludes  = []
  , optFiles     = files
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option []    ["help"]    (NoArg setHelp)  "Show help."
  , Option ['c'] ["ctags"]   (OptArg setCTagsFile "FILE") "Generate ctags (default file=tags)"
  , Option ['e'] ["etags"]   (OptArg setETagsFile "FILE") "Generate etags (default file=TAGS)"
  , Option ['i'] ["include"] (ReqArg addInclude   "FILE") "File to #include"
  ]
  where
    setHelp           o = o { optHelp      = True }
    setCTags          o = o { optCTags     = True }
    setETags          o = o { optETags     = True }
    setCTagsFile file o = o { optCTagsFile = fromMaybe "tags" file, optCTags = True }
    setETagsFile file o = o { optETagsFile = fromMaybe "TAGS" file, optETags = True }
    addInclude   file o = o { optIncludes  = file : optIncludes o }
