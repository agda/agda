{-# LANGUAGE ScopedTypeVariables #-}

-- | Pretty-print contents of an interface file.

module Main where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Foldable

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Imports        ( typeCheckMain )
import Agda.Interaction.Options        ( defaultOptions )

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty

import Agda.Utils.FileName
import qualified Agda.Utils.HashMap as HashMap

import Agda.Utils.Pretty (render)

------------------------------------------------------------------------------

main :: IO ()
main = do
  _ <- liftIO $ runTCMTop mainTCM
  return ()

mainTCM :: TCM ()
mainTCM = do
  setCommandLineOptions defaultOptions
  f <- liftIO $ absolute "Issue1168.agda"
  (i, _mw) <- typeCheckMain f
  compilerMain i

compilerMain :: Interface -> TCM ()
compilerMain i = withScope_ (iInsideScope i) $ withShowAllArguments $ disableDisplayForms $ do
  let (Sig _secs defs _rews) = iSignature i
  forM_ (HashMap.toList defs) $ \ (q, def) -> do
    let t = defType def
    doc <- prettyTCM q <+> text ":" <+> prettyTCM t
    liftIO $ putStrLn $ render doc
  -- forM_ (HashMap.toList defs) $ \ (q, def) -> do
  --   let t = defType def
  --   liftIO $ putStrLn $ show q ++ " : " ++ show t
