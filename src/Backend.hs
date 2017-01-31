module Backend (backend) where

import Agda.Compiler.Backend
import System.Console.GetOpt
import Agda.Utils.Pretty
import Control.Monad.Trans
import qualified Compiler as Mlf
import Malfunction.Print
import Text.Printf

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
          mlf <- translate q tt
          let header c h = let cs = replicate 15 c in text $ printf "%s %s %s" cs h cs
              pretty' = text . showBinding
              sect t dc = text t $+$ nest 2 dc $+$ text ""
          liftIO . putStrLn . render
            $  header '=' (show q)
            $$ sect "Treeless (abstract syntax)"    (text . show $ tt)
            $$ sect "Treeless (concrete syntax)"    (pretty tt)
            $$ sect "Malfunction (abstract syntax)" (text . show $ mlf)
            $$ sect "Malfunction (concrete syntax)" (pretty' mlf)
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
