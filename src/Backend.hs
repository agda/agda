module Backend (backend) where

import Agda.Compiler.Backend
import System.Console.GetOpt
import Agda.Utils.Pretty
import Control.Monad.Trans
import Compiler
import Malfunction.Print

backend :: Backend
backend = Backend backend'

data MlfOptions = Opts {
  _enabled :: Bool
  }

defOptions :: MlfOptions
defOptions = Opts {
  _enabled = False
  }

ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg $ \ o -> return o{ _enabled = True }) "Generate Malfunction"
  ]

backend' :: Backend' MlfOptions () () () ()
backend' = Backend' {
  backendName = "malfunction"
  , options = defOptions
  , commandLineFlags = ttFlags
  , isEnabled = _enabled
  , preCompile = const $ return ()
  , postCompile = \env isMain r -> return ()
  , preModule = \enf m ifile -> return $ Recompile ()
  , compileDef = \env menv -> mlfDef
  , postModule = \env menv m defs -> return ()
  }

mlfDef :: Definition -> TCM ()
mlfDef d@Defn{ defName = q } =
  case theDef d of
    Function{} -> do
      mtt <- toTreeless q
      case mtt of
        Nothing -> return ()
        Just tt -> do
          liftIO $ putStrLn (replicate 70 '=')
          liftIO $ putStrLn "Treeless"
          liftIO $ print $ nest 2 $ hang (pretty q <+> text "=") 2 (pretty tt)
          liftIO $ putStrLn (replicate 70 '-')
          liftIO $ putStrLn "Treeless AST"
          liftIO $ putStrLn (show q ++ " = " ++ show tt)
          liftIO $ putStrLn (replicate 70 '-')
          liftIO $ putStrLn "Malfunction AST"
          liftIO $ putStrLn (show q ++ " = " ++ showTerm (translate tt))
    Primitive{ primName = s } -> do
      liftIO $ putStrLn $ "  primitive " ++ s
    Axiom         -> return ()
    AbstractDefn  -> error "impossible"
    Datatype{}    -> liftIO $ putStrLn $ "  data " ++ show q
    Record{}      -> liftIO $ putStrLn $ "  record " ++ show q
    Constructor{} -> liftIO $ putStrLn $ "  constructor " ++ show q
