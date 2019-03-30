module Agda.Interaction.AgdaTop
    ( repl
    ) where

import Control.Monad.State
import Data.Char
import System.IO

import Agda.Interaction.Response as R
import Agda.Interaction.InteractionTop
import Agda.Interaction.Options
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.Utils.Maybe

----------------------------------

-- | 'repl' is a fake ghci interpreter for both the Emacs the JSON frontend
repl :: InteractionOutputCallback -> String -> TCM () -> TCM ()
repl callback prompt setup = do
    liftIO $ do
      hSetBuffering stdout LineBuffering
      hSetBuffering stdin  LineBuffering
      hSetEncoding  stdout utf8
      hSetEncoding  stdin  utf8

    setInteractionOutputCallback callback

    commands <- liftIO $ initialiseCommandQueue readCommand

    handleCommand_ (lift setup) `evalStateT` initCommandState commands

    opts <- commandLineOptions
    _ <- interact' `runStateT`
           (initCommandState commands)
             { optionsOnReload = opts{ optAbsoluteIncludePaths = [] } }
    return ()
  where
  interact' :: CommandM ()
  interact' = do
    Bench.reset
    done <- Bench.billTo [] $ do

      liftIO $ do
        putStr prompt
        hFlush stdout
      r <- maybeAbort runInteraction
      case r of
        Done      -> return True -- Done.
        Error s   -> liftIO (putStrLn s) >> return False
        Command _ -> return False

    lift Bench.print
    unless done interact'

  -- Reads the next command from stdin.

  readCommand :: IO Command
  readCommand = do
    done <- isEOF
    if done then
      return Done
    else do
      r <- getLine
      _ <- return $! length r     -- force to read the full input line
      case dropWhile isSpace r of
        ""          -> readCommand
        ('-':'-':_) -> readCommand
        _           -> case listToMaybe $ reads r of
          Just (x, "")  -> return $ Command x
          Just (_, rem) -> return $ Error $ "not consumed: " ++ rem
          _             -> return $ Error $ "cannot read: " ++ r
