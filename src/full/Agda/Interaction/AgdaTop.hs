module Agda.Interaction.AgdaTop
    ( repl
    ) where

import Control.Monad                ( unless )
import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.State          ( evalStateT, runStateT )
import Control.Monad.Trans          ( lift )

import Data.Char
import Data.Maybe
import System.IO

import Agda.Interaction.Base
import Agda.Interaction.ExitCode
import Agda.Interaction.Response as R
import Agda.Interaction.InteractionTop
import Agda.Interaction.Options
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

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
        Command _ -> return False
        Error s   -> do
          exit <- optExitOnError <$> commandLineOptions
          if exit
            then liftIO (exitAgdaWith CommandError)
            else do
              liftIO (putStrLn s)
              return False

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
        _           -> case parseIOTCM r of
          Right cmd -> return $ Command cmd
          Left err  -> return $ Error err
