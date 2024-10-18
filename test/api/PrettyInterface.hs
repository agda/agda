{-# LANGUAGE ScopedTypeVariables #-}

-- | Pretty-print contents of an interface file.

module Main where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Foldable
import qualified Data.HashMap.Strict as HashMap

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Imports ( typeCheckMain, Mode(TypeCheck), parseSource, CheckResult(CheckResult), crInterface )
import Agda.Interaction.Options ( defaultOptions )

import Agda.TypeChecking.Monad   ( TCM, Definition(..), Interface(..), Signature(..), runTCMTop, setCommandLineOptions, srcFromPath, withScope_  )
import Agda.TypeChecking.Pretty  ( prettyTCM, (<+>), text )

import Agda.Utils.FileName       ( absolute )

import Agda.Syntax.Common.Pretty (render )

------------------------------------------------------------------------------

main :: IO ()
main = do
  _ <- liftIO $ runTCMTop mainTCM
  return ()

mainTCM :: TCM ()
mainTCM = do
  setCommandLineOptions defaultOptions
  f   <- liftIO $ absolute "PrettyInterface.agda"
  src <- srcFromPath f
  CheckResult { crInterface = i } <- typeCheckMain TypeCheck =<< parseSource src
  compilerMain i

compilerMain :: Interface -> TCM ()
compilerMain i = withScope_ (iInsideScope i) $ do -- withShowAllArguments $ disableDisplayForms $ do
  let Sig{_sigDefinitions = defs} = iSignature i
  forM_ (HashMap.toList defs) $ \ (q, def) -> do
    let t = defType def
    doc <- prettyTCM q <+> text ":" <+> prettyTCM t
    liftIO $ putStrLn $ render doc
  -- forM_ (HashMap.toList defs) $ \ (q, def) -> do
  --   let t = defType def
  --   ast <- reify t
  --   liftIO $ putStrLn $ show q ++ " : " ++ show t
  --   return $ const () ast
