module Backend (backend) where

import Agda.Compiler.Backend
import System.Console.GetOpt
import Agda.Utils.Pretty
import Control.Monad.Trans
import qualified Compiler as Mlf
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
          liftIO . putStrLn . unlines $
            [ replicate 70 '='
            , "Treeless"
            , show $ nest 2 $ hang (pretty q <+> text "=") 2 (pretty tt)
            , replicate 70 '-'
            , "Treeless AST"
            , show q ++ " = " ++ show tt
            , replicate 70 '-'
            ]
          -- Now attempting the impossible.
          mlf <- translate q tt
          liftIO . putStrLn . unlines $
            [ "Malfunction AST"
            , showBinding mlf
            ]
    Primitive{ primName = s } ->
      liftIO $ putStrLn $ "  primitive " ++ s
    Axiom         -> return ()
    AbstractDefn  -> error "impossible"
    Datatype{}    -> liftIO $ putStrLn $ "  data " ++ show q
    Record{}      -> liftIO $ putStrLn $ "  record " ++ show q
    Constructor{} -> liftIO $ putStrLn $ "  constructor " ++ show q

-- TODO: Can we somehow extract functionality from the TCM-monad and pass
-- it to Mlf.translate? I was thinking that if all we need from the TCM-
-- monad is a way to translate from names to identifiers, then perhaps we
-- could extract such a lookup-function and use it in MonadTranslate.
translate :: QName -> TTerm -> TCMT IO Mlf.Binding
translate nm = return . Mlf.translateDef nm
