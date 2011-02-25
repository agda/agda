{-# LANGUAGE CPP #-}
module Agda.Interaction.Highlighting.Dot where

import Control.Applicative
import Control.Monad.State

import qualified Data.Map as M
import Data.Map(Map)
import Data.Maybe
import Data.Monoid

import qualified Data.Set as S
import Data.Set (Set)

import System.Directory
import System.FilePath

import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Syntax.Abstract
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad

import Agda.Utils.FileName


#include "../../undefined.h"
import Agda.Utils.Impossible

data DotState = DotState
  { dsModules    :: Map ModuleName String
  , dsNameSupply :: [String]
  , dsConnection :: Set (String, String)
  }

initialDotState :: DotState
initialDotState = DotState
  { dsModules    = mempty
  , dsNameSupply = map (('m':) . show) [0..]
  , dsConnection = mempty
  }

type DotM = StateT DotState TCM

addModule :: ModuleName -> DotM (String, Bool)
addModule m = do
    s <- get
    case M.lookup m (dsModules s) of
        Just r  -> return (r, False)
        Nothing -> do
            let newName:nameSupply = dsNameSupply s
            put s
              { dsModules = M.insert m newName (dsModules s)
              , dsNameSupply = nameSupply
              }
            return (newName, True)


addConnection :: String -> String -> DotM ()
addConnection m1 m2 = modify $ \s -> s {dsConnection = S.insert (m1,m2) (dsConnection s)}

dottify :: Interface -> DotM String
dottify inter = do
    let curModule = iModuleName inter
    (name, continue) <- addModule curModule
    importsifs <- lift $ map miInterface . catMaybes <$> mapM (getVisitedModule . toTopLevelModuleName) (iImportedModules inter)
    when continue $ do
        imports    <- mapM dottify importsifs
        mapM_ (addConnection name) imports
    return name


generateDot :: Interface -> TCM ()
generateDot inter = do
    (top, state) <- flip runStateT initialDotState $ do
        dottify inter
    mfile <- optDependencyGraph <$> commandLineOptions
    case mfile of
        Nothing -> __IMPOSSIBLE__
        Just fp -> liftIO $ writeFile fp $ mkDot state
  where
    mkDot :: DotState -> String
    mkDot st = unlines $
        [ "digraph dependencies {"
        ] ++ ["   " ++ repr ++ "[label=\"" ++ show modulename ++ "\"];"
             | (modulename, repr) <- M.toList (dsModules st)]
          ++ ["   " ++ r1 ++ " -> " ++ r2 ++ ";"
             | (r1 , r2) <- S.toList (dsConnection st) ]
          ++ ["}"]
