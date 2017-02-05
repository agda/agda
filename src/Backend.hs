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
import           Malfunction.Run
import           System.Console.GetOpt
import           Text.Printf

backend :: Backend
backend = Backend backend'

data MlfOptions = Opts {
  _enabled :: Bool
  , _resultVar :: Maybe Ident
  }

defOptions :: MlfOptions
defOptions = Opts {
  _enabled = False
  , _resultVar = Nothing
  }

ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg $ \ o -> return o{ _enabled = True })
    "Generate Malfunction"
  , Option ['r'] [] (ReqArg (\r o -> return o{_resultVar = Just r}) "VAR")
    "(DEBUG) Run the module and print the integer value of a variable"
  ]

backend' :: Backend' MlfOptions MlfOptions () Mod Definition
backend' = Backend' {
  backendName = "malfunction"
  , options = defOptions
  , commandLineFlags = ttFlags
  , isEnabled = _enabled
  , preCompile = return
  , postCompile = \env isMain r -> liftIO (putStrLn "post compile")
  , preModule = \enf m ifile -> return $ Recompile ()
  , compileDef = \env menv -> return
  , postModule = \env menv m mod defs -> mlfModule env defs
  , backendVersion = Nothing
  }

mlfModule :: MlfOptions -> [Definition] -> TCM Mod
mlfModule mlfopt defs = do
  mlfMod <- (`MMod`[]) . catMaybes <$> mapM (mlfDef defs) defs
  liftIO (putStrLn (showMod mlfMod))
  printRes mlfMod
  return mlfMod
  where defns = map theDef defs
        printRes mlfMod@(MMod binds _) = do
          liftIO (putStrLn "\n=======================")
          liftIO (case _resultVar mlfopt of
                    Just var
                      | any defVar binds -> runModPrintInts [var] mlfMod >>= putStrLn
                      where defVar (Named v _) = v == var
                            defVar _ = False
                    _ -> return ())

mlfDef :: [Definition] -> Definition -> TCM (Maybe Binding)
mlfDef alldefs d@Defn{ defName = q } =
  case theDef d of
    Function{} -> do
      mtt <- toTreeless q
      case mtt of
        Nothing -> return Nothing
        Just tt -> do
          liftIO . putStrLn . render
            $  header '=' (show q)
            $$ sect "Treeless (abstract syntax)"    (text . show $ tt)
            $$ sect "Treeless (concrete syntax)"    (pretty tt)
          let
            mlf = Mlf.translateDef' (getConstructors alldefs) q tt
            pretty' = text . showBinding
          liftIO . putStrLn . render $
            sect "Malfunction (abstract syntax)" (text . show $ mlf)
            $$ sect "Malfunction (concrete syntax)" (pretty' mlf)
          return (Just mlf)
            where
              sect t dc = text t $+$ nest 2 dc $+$ text ""
              header c h = let cs = replicate 15 c
                           in text $ printf "%s %s %s" cs h cs

    Primitive{ primName = s } ->
      liftIO (putStrLn $ "  primitive " ++ s) >> return Nothing
    Axiom         -> return Nothing
    AbstractDefn  -> error "impossible"
    Datatype{}    -> liftIO (putStrLn $ "  data " ++ show q) >> return Nothing
    Record{}      -> liftIO (putStrLn $ "  record " ++ show q) >> return Nothing
    Constructor{} -> liftIO (putStrLn $ "  constructor " ++ show q) >> return Nothing

-- | Returns a list of constructor names grouped by data type
getConstructors :: [Definition] -> [[QName]]
getConstructors = map (getCons . theDef)
  where
    getCons :: Defn -> [QName]
    getCons c@Datatype{} = dataCons c
    getCons _ = []
