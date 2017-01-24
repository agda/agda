{-# LANGUAGE RankNTypes, TupleSections #-}
-- Testing backend hooks using Agda as a library. Test case: treeless backend.
module Main where

-- import Data.Map (Map)
-- import qualified Data.Map as Map

import Control.Monad.Trans
import System.Console.GetOpt

import Agda.Compiler.Backend
import Agda.Utils.Pretty
import Agda.Main (runTCMPrettyErrors)

-- Treeless backend -------------------------------------------------------

data TreelessOptions = TreelessOptions
  { ttEnabled :: Bool }

treelessOptions = TreelessOptions
  { ttEnabled = False }

ttFlags :: [OptDescr (Flag TreelessOptions)]
ttFlags =
  [ Option [] ["tt"] (NoArg $ \ o -> return o{ ttEnabled = True }) "Generate treeless"
  ]

treelessDef :: Definition -> TCM ()
treelessDef d@Defn{ defName = q } =
  case theDef d of
    Function{} -> do
      mtt <- toTreeless q
      case mtt of
        Nothing -> return ()
        Just tt -> liftIO $ print $ nest 2 $ hang (pretty q <+> text "=") 2 (pretty tt)
    Primitive{ primName = s } -> do
      liftIO $ putStrLn $ "  primitive " ++ s
    Axiom         -> return ()
    AbstractDefn  -> error "impossible"
    Datatype{}    -> liftIO $ putStrLn $ "  data " ++ show q
    Record{}      -> liftIO $ putStrLn $ "  record " ++ show q
    Constructor{} -> liftIO $ putStrLn $ "  constructor " ++ show q

treelessBackend :: Backend
treelessBackend = Backend $ Backend'
  { backendName      = "Treeless"
  , options          = treelessOptions
  , commandLineFlags = ttFlags
  , isEnabled        = ttEnabled
  , preCompile       = \ opts            -> return ()
  , postCompile      = \ env isMain r    -> return ()
  , preModule        = \ env m ifile     -> Recompile () <$ liftIO (putStrLn $ "Compiling " ++ show m)
  , compileDef       = \ env menv        -> treelessDef
  , postModule       = \ env menv m defs -> return ()
  }

main :: IO ()
main = runAgda [treelessBackend]

