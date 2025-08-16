{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Read the scope of an interface file.

module Main where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad               ( forM_, (<$!>) )
import Control.Monad.IO.Class      ( liftIO )
import Control.Monad.Except
import Control.Monad.Trans.Maybe

import qualified Data.ByteString as BS
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import System.Environment ( getArgs )
------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Options  ( defaultOptions )

import Agda.Syntax.Abstract.Name ( ModuleName )
import Agda.Syntax.Scope.Base    ( Scope, ScopeInfo, publicModules )

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.Serialise.Base

import Agda.Utils.Hash           ( Hash )
import Agda.Syntax.Common.Pretty
import Agda.Utils.Impossible


------------------------------------------------------------------------------

data TruncatedInterface = TruncatedInterface
  { tiSourceHash      :: Hash
    -- ^ Hash of the source code.
  , tiImportedModules :: [(ModuleName, Hash)]
    -- ^ Imported modules and their hashes.
  , tiModuleName      :: ModuleName
    -- ^ Module name of this interface.
  , tiScope           :: Map ModuleName Scope
    -- ^ Scope defined by this module. (Not serialized.)
  , tiInsideScope     :: ScopeInfo
    -- ^ Scope after we loaded this interface.
  }

instance EmbPrj TruncatedInterface where
  icod_ = __IMPOSSIBLE__
  value = vcase $ \case
    N5 a b c d e     -> valuN TruncatedInterface a b c d e
    N6 a b c d e _ _ -> valuN TruncatedInterface a b c d e
    _                -> __IMPOSSIBLE__

------------------------------------------------------------------------------

main :: IO ()
main = do
  _ <- liftIO . runTCMTop . mainTCM =<< getArgs
  return ()

mainTCM :: [String] -> TCM ()
mainTCM args = do
  setCommandLineOptions defaultOptions
  let f = fromMaybe "ScopeFromInterface.agdai" $ listToMaybe args
  readTruncatedInterface f >>= \case
    Just i -> processInterface i
    Nothing -> throwError $ GenericException "Cannot read interface file"

processInterface :: TruncatedInterface -> TCM ()
processInterface i = liftIO $ do
  -- print $ tiSourceHash i
  -- print $ tiImportedModules i
  -- print $ tiModuleName i
  -- print $ tiScope i
  -- putStrLn $ "Number of public modules: " ++ show (Map.size $ tiScope i)
  -- putStrLn $ render $ pretty $ tiInsideScope i
  -- print $ tiInsideScope i

  putStrLn "Imported modules:"
  mapM_ putStrLn $ List.sort $ map (render . pretty . fst) $ tiImportedModules i
  putStrLn ""
  -- putStrLn "Scope"
  forM_ (Map.toList $ tiScope i) $ \ (_m, s) -> do
    putStrLn $ render $ pretty s

-- | Copy-and-paste from 'Agda.Interaction.Imports.readInterface'.
readTruncatedInterface :: String -> TCM (Maybe TruncatedInterface)
readTruncatedInterface file = do
    bstr <- (liftIO $ Just <$!> BS.readFile file) `catchError` \case
      IOException _ _ e -> do
        alwaysReportSLn "" 0 $ "IO exception: " ++ show e
        return Nothing   -- Work-around for file locking bug.
                         -- TODO: What does this refer to? Please
                         -- document.
      e -> throwError e
    case bstr of
      Just bstr -> runMaybeT $ do
        ti <- decode =<< deserializeInterface bstr
        pure $ ti {tiScope = publicModules $ tiInsideScope ti}
      Nothing -> pure Nothing
