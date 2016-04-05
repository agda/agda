module AgdaPkg.Internal where

import Control.Monad.Trans

import System.FilePath
import System.Directory
import System.Process
import Data.Version
import Control.Monad.Catch
import Data.List

import Paths_Agda

import Agda.Packaging.Base
import Agda.Packaging.Database
import Agda.Utils.IO.Directory

import AgdaPkg.Build
import AgdaPkg.Monad
import AgdaPkg.Error



initPackageDB :: (MonadThrow m, MonadIO m) => FilePath -> m ()
initPackageDB pkgDir = liftIO $ do
  pkgDir <- exceptTToThrow GenericAgdaPkgError $ packageDBPath pkgDir
  putStrLn $ "Creating Agda package db in " ++ pkgDir ++ " ..."


replace :: String -> String -> String -> String
replace _ _ [] = []
replace s r (x:xs)
  | s `isPrefixOf` xs = r ++ replace s r (drop (length s) xs)
  | otherwise         = x : replace s r xs

