{-# OPTIONS -fglasgow-exts #-}

{-| This modules deals with how to find imported modules and loading their
    interface files.
-}
module Interaction.Imports where

import Control.Monad
import Control.Monad.State
import Control.Exception
import Data.Typeable
import qualified Data.Map as Map
import System.Directory

import Syntax.Position
import Syntax.Concrete as C
import Syntax.Abstract as A
import Syntax.Parser

-- Exceptions -------------------------------------------------------------

data ImportException
	= FileNotFound C.QName [FilePath]
	    -- ^ Couldn't find the module (@QName@) even though I looked
	    --	 everywhere (@[FilePath]@).
    deriving (Typeable, Show)

instance HasRange ImportException where
    getRange (FileNotFound x _) = getRange x

fileNotFound x paths = throwDyn $ FileNotFound x paths

-- | Parameterised to avoid cyclic module dependencies.
scopeCheckModule :: MonadIO m => (C.Declaration -> m scopeInfo) -> C.QName -> m scopeInfo
scopeCheckModule concreteToAbstract_ x = do
    m <- liftIO $ do
	exists <- liftIO $ doesFileExist file
	unless exists $ fileNotFound x [file]
	(_, m)     <- parseFile' moduleParser file
	return m
    scope <- concreteToAbstract_ m
    return scope
    where
	file = moduleNameToFileName x ".agda"

{-| Look for an interface file for the given module. In the future this
    function will check that the interface is up-to-date and otherwise re-type
    check the module. It will also consult the command line options and other
    appropriate sources to find a reasonable path to look in. At the moment it
    looks in the current directory and fails if there isn't an interface file
    there (or in the expected subdirectory).

    TODO: the suffix for interface files is hard-wired to @.agdai@.
-}
getModuleInterface :: MonadIO m => C.QName -> m a
getModuleInterface x = liftIO $ do
    fail "imports doesn't work"
    where
	file = moduleNameToFileName x ".agdai"

-- | Put some of this stuff in a Utils.File
type Suffix = String

{-| Turn a module name into a file name with the given suffix.
    
    TODO: Uses @\/@ as path separator. This should be configured, or wait.. all
	  platforms that supports configure uses @\/@. Hm.. anyway it shouldn't
	  be hard-wired. We have to think about Windows compatibilty at some
	  point.
-}
moduleNameToFileName :: C.QName -> Suffix -> FilePath
moduleNameToFileName (C.QName x) ext = show x ++ ext
moduleNameToFileName (Qual m  x) ext = show m ++ "/" ++ moduleNameToFileName x ext

