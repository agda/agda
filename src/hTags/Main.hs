{-# LANGUAGE PatternSignatures #-}

module Main where

import Control.Applicative
import Control.Exception
import Control.Monad
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
import Parser
import Lexer
import DriverPipeline
import FastString
import DriverPhases
import StringBuffer
import SrcLoc
import Outputable

import Tags

fileLoc :: FilePath -> SrcLoc
fileLoc file = mkSrcLoc (mkZFastString file) 1 1

filePState :: DynFlags -> FilePath -> IO PState
filePState dflags file = do
  buf <- hGetStringBuffer file
  return $ mkPState buf (fileLoc file) dflags

pMod :: P (Located (HsModule RdrName))
pMod = parseModule

parse :: PState -> P a -> ParseResult a
parse st p = unP p st

debug = hPutStrLn stderr

goFile :: Session -> FilePath -> IO [Tag]
goFile session file = do
  dflags <- getSessionDynFlags session
  (dflags, srcFile) <- preprocess dflags (file, Just $ Cpp HsSrcFile)
    `catchDyn` \(e :: GhcException) -> do
      debug $ "panic: " ++ show e
      exitWith $ ExitFailure 1
  st <- filePState dflags srcFile
  case parse st parseModule of
    POk _ m   -> return $ tags $ unLoc m
    PFailed loc err -> do
      let file = unpackFS $ srcLocFile $ srcSpanStart loc
          line = srcSpanStartLine loc
      debug $ file ++ ":" ++ show line
      debug $ show $ err defaultDumpStyle
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
         | optETags opts = do
            debug $ "etags not supported"
            exitWith $ ExitFailure 1
         | otherwise = do
            top : _ <- lines <$> runCmd "ghc --print-libdir"
            session <- newSession (Just top)
            -- This looks like a no-op but it's actually not.
            -- setSessionDynFlags does interesting (and necessary) things.
            setSessionDynFlags session =<< getSessionDynFlags session
            ts <- mapM (goFile session) $ optFiles opts
            let sts = sort $ concat ts
            when (optCTags opts) $
              writeFile (optCTagsFile opts) $ unlines $ map show sts
  go

getOptions :: IO Options
getOptions = do
  args <- getArgs
  case getOpt Permute options args of
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
  , optFiles     :: [FilePath]
  }

defaultOptions :: [FilePath] -> Options
defaultOptions files = Options
  { optCTags     = True
  , optETags     = False
  , optCTagsFile = "tags"
  , optETagsFile = "TAGS"
  , optHelp      = False
  , optFiles     = files
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option []    ["help"]  (NoArg setHelp)  "Show help."
  , Option ['c'] ["ctags"] (OptArg setCTagsFile "FILE") "Generate ctags (default) (default file=tags)"
  , Option ['e'] ["etags"] (OptArg setETagsFile "FILE") "Generate etags (default file=TAGS)"
  ]
  where
    setHelp           o = o { optHelp      = True }
    setCTags          o = o { optCTags     = True }
    setETags          o = o { optETags     = True }
    setCTagsFile file o = o { optCTagsFile = fromMaybe "tags" file, optCTags = True }
    setETagsFile file o = o { optETagsFile = fromMaybe "TAGS" file, optETags = True }


