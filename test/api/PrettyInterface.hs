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

import Agda.Interaction.FindFile ( SourceFile(..) )
import Agda.Interaction.Imports ( typeCheckMain, Mode(TypeCheck), parseSource, CheckResult(CheckResult), crInterface )
import Agda.Interaction.Options ( defaultOptions )

-- import Agda.Syntax.Translation.InternalToAbstract ( reify )
-- import Agda.Syntax.Translation.AbstractToConcrete ()

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty

import Agda.Utils.FileName

import Agda.Syntax.Common.Pretty (render)

------------------------------------------------------------------------------

main :: IO ()
main = do
  _ <- liftIO $ runTCMTop mainTCM
  return ()

mainTCM :: TCM ()
mainTCM = do
  setCommandLineOptions defaultOptions
  f <- liftIO $ SourceFile <$> absolute "PrettyInterface.agda"
  CheckResult { crInterface = i } <- typeCheckMain TypeCheck =<< parseSource f
  compilerMain i

compilerMain :: Interface -> TCM ()
compilerMain i = withScope_ (iInsideScope i) $ do -- withShowAllArguments $ disableDisplayForms $ do
  let (Sig _secs defs _rews) = iSignature i
  forM_ (HashMap.toList defs) $ \ (q, def) -> do
    let t = defType def
    doc <- prettyTCM q <+> text ":" <+> prettyTCM t
    liftIO $ putStrLn $ render doc
  -- forM_ (HashMap.toList defs) $ \ (q, def) -> do
  --   let t = defType def
  --   ast <- reify t
  --   liftIO $ putStrLn $ show q ++ " : " ++ show t
  --   return $ const () ast
