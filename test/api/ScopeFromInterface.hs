{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Read the scope of an interface file.

module Main where

------------------------------------------------------------------------------
-- Haskell imports

import qualified Control.Exception as E
import Control.Monad.Except

import qualified Data.ByteString.Lazy as BS
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Typeable (Typeable)

import System.Environment ( getArgs )
------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Options  ( defaultOptions )

import Agda.Syntax.Abstract.Name ( ModuleName )
import Agda.Syntax.Scope.Base    ( Scope, ScopeInfo, publicModules )

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.Serialise.Base

import Agda.Utils.Functor
import Agda.Utils.Hash           ( Hash )
import Agda.Utils.IO.Binary      ( readBinaryFile' )
import Agda.Utils.List           ( headMaybe )
import Agda.Utils.Null
import Agda.Utils.Pretty
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
  } deriving (Typeable)

instance EmbPrj TruncatedInterface where
  icod_ = __IMPOSSIBLE__
  value = vcase $ \case
    (a : b : c : d : e : _) -> valuN TruncatedInterface a b c d e
    _ -> __IMPOSSIBLE__

------------------------------------------------------------------------------

main :: IO ()
main = do
  _ <- liftIO . runTCMTop . mainTCM =<< getArgs
  return ()

mainTCM :: [String] -> TCM ()
mainTCM args = do
  setCommandLineOptions defaultOptions
  let f = fromMaybe "ScopeFromInterface.agdai" $ headMaybe args
  readTruncatedInterface f >>= \case
    Just i -> processInterface i
    Nothing -> throwError $ Exception empty $ text "Cannot read interface file"

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

-- | Cut-and-paste from 'Agda.Interaction.Imports.readInterface'.

readTruncatedInterface :: FilePath -> TCM (Maybe TruncatedInterface)
readTruncatedInterface file = do
    -- Decode the interface file
    (s, close) <- liftIO $ readBinaryFile' file
    do  mi <- liftIO . E.evaluate =<< decodeTruncatedInterface s

        -- Close the file. Note
        -- ⑴ that evaluate ensures that i is evaluated to WHNF (before
        --   the next IO operation is executed), and
        -- ⑵ that decode returns Nothing if an error is encountered,
        -- so it is safe to close the file here.
        liftIO close

        -- Reconstruct @iScope@.
        return $ mi <&> \ i -> i{ tiScope = publicModules $ tiInsideScope i }
      -- Catch exceptions and close
      `catchError` \e -> liftIO close >> handler e
  -- Catch exceptions
  `catchError` handler
  where
    handler = \case
      IOException _ _ e -> do
        reportSLn "" 0 $ "IO exception: " ++ show e
        return Nothing   -- Work-around for file locking bug.
                         -- TODO: What does this refer to? Please
                         -- document.
      e -> throwError e

-- | Cut-and-paste from 'Agda.TypeChecking.Serialize.decodeInterface'.

decodeTruncatedInterface :: BS.ByteString -> TCM (Maybe TruncatedInterface)
decodeTruncatedInterface s = decode $ BS.drop 16 s
