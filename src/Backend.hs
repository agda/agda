module Backend (backend) where

import           Agda.Compiler.Backend
import           Agda.Syntax.Internal
import           Agda.Utils.Pretty
import qualified Compiler as Mlf
import           Control.Monad.Trans
import           Data.List.Extra
import           Data.Maybe
import           Malfunction.AST
import           Malfunction.Print
import           System.Console.GetOpt
import           Text.Printf

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

backend' :: Backend' MlfOptions () () Mod Definition
backend' = Backend' {
  backendName = "malfunction"
  , options = defOptions
  , commandLineFlags = ttFlags
  , isEnabled = _enabled
  , preCompile = const $ return ()
  , postCompile = \env isMain r -> liftIO (putStrLn "post compile")
  , preModule = \enf m ifile -> return $ Recompile ()
  , compileDef = \env menv -> return
  , postModule = \env menv m mod -> mlfModule
  , backendVersion = Nothing
  }

mlfModule :: [Definition] -> TCM Mod
mlfModule defs = do
  mlfMod <- (`MMod`[]) . catMaybes <$> mapM mlfDef defs
  liftIO (putStrLn (showMod mlfMod))
  return mlfMod

mlfDef :: Definition -> TCM (Maybe Binding)
mlfDef d@Defn{ defName = q } =
  case theDef d of
    Function{} -> do
      mtt <- toTreeless q
      case mtt of
        Nothing -> return Nothing
        Just tt -> do
          let mlf = Mlf.translateDef q tt
              header c h = let cs = replicate 15 c
                           in text $ printf "%s %s %s" cs h cs
              pretty' = text . showBinding
              sect t dc = text t $+$ nest 2 dc $+$ text ""
          liftIO . putStrLn . render
            $  header '=' (show q)
            $$ sect "Treeless (abstract syntax)"    (text . show $ tt)
            $$ sect "Treeless (concrete syntax)"    (pretty tt)
            $$ sect "Malfunction (abstract syntax)" (text . show $ mlf)
            $$ sect "Malfunction (concrete syntax)" (pretty' mlf)
          return (Just mlf)
    Primitive{ primName = s } ->
      liftIO (putStrLn $ "  primitive " ++ s) >> return Nothing
    Axiom         -> return Nothing
    AbstractDefn  -> error "impossible"
    Datatype{}    -> liftIO (putStrLn $ "  data " ++ show q) >> return Nothing
    Record{}      -> liftIO (putStrLn $ "  record " ++ show q) >> return Nothing
    c@Constructor{} -> do
      liftIO (putStrLn $ "  constructor " ++ show q)
      liftIO (putStrLn $ "conSrcCon " ++ show (conName $ conSrcCon c))
      return Nothing

-- | Returns a list of constructor names grouped by data type
getConstructors :: [Defn] -> [[QName]]
getConstructors = map snd . groupSort . mapMaybe getCons
  where
    getCons :: Defn -> Maybe (QName, QName)
    getCons c@Constructor{} = Just (conData c, conName (conSrcCon c))
    getCons _ = Nothing

-- TODO: Can we somehow extract functionality from the TCM-monad and pass
-- it to Mlf.translate? I was thinking that if all we need from the TCM-
-- monad is a way to translate from names to identifiers, then perhaps we
-- could extract such a lookup-function and use it in MonadTranslate.
-- translate :: QName -> TTerm -> TCMT IO Mlf.Binding
-- translate nm = return . Mlf.translateDef nm
