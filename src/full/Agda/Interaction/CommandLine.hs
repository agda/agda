
module Agda.Interaction.CommandLine
  ( runInteractionLoop
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.State
import Control.Monad.Reader

import qualified Data.List as List
import Data.Maybe

import Text.Read (readMaybe)

import Agda.Interaction.Base hiding (Command)
import Agda.Interaction.BasicOps as BasicOps hiding (parseExpr)
import Agda.Interaction.Imports ( CheckResult, crInterface )
import Agda.Interaction.Monad

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal (telToList, alwaysUnblock)
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Abstract.Pretty

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Pretty ( PrettyTCM(prettyTCM) )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Warnings (runPM)

import Agda.Utils.FileName (absolute, AbsolutePath)
import Agda.Utils.Pretty

import Agda.Utils.Impossible

data ReplEnv = ReplEnv
    { replSetupAction     :: TCM ()
    , replTypeCheckAction :: AbsolutePath -> TCM CheckResult
    }

data ReplState = ReplState
    { currentFile :: Maybe AbsolutePath
    }

newtype ReplM a = ReplM { unReplM :: ReaderT ReplEnv (StateT ReplState IM) a }
    deriving
    ( Functor, Applicative, Monad, MonadIO
    , HasOptions, MonadTCEnv, ReadTCState, MonadTCState, MonadTCM
    , MonadError TCErr
    , MonadReader ReplEnv, MonadState ReplState
    )

runReplM :: Maybe AbsolutePath -> TCM () -> (AbsolutePath -> TCM CheckResult) -> ReplM () -> TCM ()
runReplM initialFile setup checkInterface
    = runIM
    . flip evalStateT (ReplState initialFile)
    . flip runReaderT replEnv
    . unReplM
  where
  replEnv = ReplEnv
    { replSetupAction     = setup
    , replTypeCheckAction = checkInterface
    }

data ExitCode a = Continue | ContinueIn TCEnv | Return a

type Command a = (String, [String] -> ReplM (ExitCode a))

matchCommand :: String -> [Command a] -> Either [String] ([String] -> ReplM (ExitCode a))
matchCommand x cmds =
    case List.filter (List.isPrefixOf x . fst) cmds of
        [(_,m)] -> Right m
        xs      -> Left $ List.map fst xs

interaction :: String -> [Command a] -> (String -> TCM (ExitCode a)) -> ReplM a
interaction prompt cmds eval = loop
    where
        go (Return x)       = return x
        go Continue         = loop
        go (ContinueIn env) = localTC (const env) loop

        loop =
            do  ms <- ReplM $ lift $ lift $ readline prompt
                case fmap words ms of
                    Nothing               -> return $ error "** EOF **"
                    Just []               -> loop
                    Just ((':':cmd):args) ->
                        do  case matchCommand cmd cmds of
                                Right c -> go =<< (c args)
                                Left [] ->
                                    do  liftIO $ putStrLn $ "Unknown command '" ++ cmd ++ "'"
                                        loop
                                Left xs ->
                                    do  liftIO $ putStrLn $ "More than one command match: " ++
                                                            List.intercalate ", " xs
                                        loop
                    Just _ ->
                        do  go =<< liftTCM (eval $ fromJust ms)
            `catchError` \e ->
                do  s <- prettyError e
                    liftIO $ putStrLn s
                    loop

runInteractionLoop :: Maybe AbsolutePath -> TCM () -> (AbsolutePath -> TCM CheckResult) -> TCM ()
runInteractionLoop initialFile setup check = runReplM initialFile setup check interactionLoop

replSetup :: ReplM ()
replSetup = do
    liftTCM =<< asks replSetupAction
    liftIO $ putStr splashScreen

checkCurrentFile :: ReplM (Maybe CheckResult)
checkCurrentFile = traverse checkFile =<< gets currentFile

checkFile :: AbsolutePath -> ReplM CheckResult
checkFile file = liftTCM . ($ file) =<< asks replTypeCheckAction

-- | The interaction loop.
interactionLoop :: ReplM ()
interactionLoop = do
    -- Run the setup action
    replSetup
    reload
    interaction "Main> " commands evalTerm
    where
        reload :: ReplM () = do
            checked <- checkCurrentFile
            liftTCM $ setScope $ maybe emptyScopeInfo (iInsideScope . crInterface) checked
            -- Andreas, 2021-01-27, issue #5132, make Set and Prop available from Agda.Primitive
            -- if no module is loaded.
            when (isNothing checked) $ do
              -- @open import Agda.Primitive using (Set; Prop)@
              void $ liftTCM importPrimitives
          `catchError` \e -> do
            s <- prettyError e
            liftIO $ putStrLn s
            liftIO $ putStrLn "Failed."

        commands =
            [ "quit"        |>  \_ -> return $ Return ()
            , "?"           |>  \_ -> continueAfter $ liftIO $ help commands
            , "reload"      |>  \_ -> do reload
                                         ContinueIn <$> askTC
            , "constraints" |> \args -> continueAfter $ liftTCM $ showConstraints args
            , "Context"     |> \args -> continueAfter $ liftTCM $ showContext args
            , "give"        |> \args -> continueAfter $ liftTCM $ giveMeta args
            , "Refine"      |> \args -> continueAfter $ liftTCM $ refineMeta args
            , "metas"       |> \args -> continueAfter $ liftTCM $ showMetas args
            , "load"        |> \args -> continueAfter $ loadFile reload args
            , "eval"        |> \args -> continueAfter $ liftTCM $ evalIn args
            , "typeOf"      |> \args -> continueAfter $ liftTCM $ typeOf args
            , "typeIn"      |> \args -> continueAfter $ liftTCM $ typeIn args
            , "wakeup"      |> \_ -> continueAfter $ liftTCM $ retryConstraints
            , "scope"       |> \_ -> continueAfter $ liftTCM $ showScope
            ]
            where
                (|>) = (,)

continueAfter :: ReplM a -> ReplM (ExitCode b)
continueAfter m = withCurrentFile $ do
  m >> return Continue

-- | Set 'envCurrentPath' to the repl's current file
withCurrentFile :: ReplM a -> ReplM a
withCurrentFile cont = do
  mpath <- gets currentFile
  localTC (\ e -> e { envCurrentPath = mpath }) cont

loadFile :: ReplM () -> [String] -> ReplM ()
loadFile reload [file] = do
  absPath <- liftIO $ absolute file
  modify (\(ReplState _prevFile) -> ReplState (Just absPath))
  withCurrentFile reload
loadFile _ _ = liftIO $ putStrLn ":load file"

showConstraints :: [String] -> TCM ()
showConstraints [] =
    do  cs <- BasicOps.getConstraints
        liftIO $ putStrLn $ unlines (List.map prettyShow cs)
showConstraints _ = liftIO $ putStrLn ":constraints [cid]"


showMetas :: [String] -> TCM ()
showMetas [m] =
    do  i <- InteractionId <$> readM m
        withInteractionId i $ do
          s <- typeOfMeta AsIs i
          r <- getInteractionRange i
          d <- prettyA s
          liftIO $ putStrLn $ render d ++ " " ++ prettyShow r
showMetas [m,"normal"] =
    do  i <- InteractionId <$> readM m
        withInteractionId i $ do
          s <- prettyA =<< typeOfMeta Normalised i
          r <- getInteractionRange i
          liftIO $ putStrLn $ render s ++ " " ++ prettyShow r
showMetas [] =
    do  interactionMetas <- typesOfVisibleMetas AsIs
        hiddenMetas      <- typesOfHiddenMetas  AsIs
        mapM_ (liftIO . print) =<< mapM showII interactionMetas
        mapM_ print' hiddenMetas
    where
        showII o = withInteractionId (outputFormId $ OutputForm noRange [] alwaysUnblock o) $ prettyA o
        showM  o = withMetaId (nmid $ outputFormId $ OutputForm noRange [] alwaysUnblock o) $ prettyA o

        metaId (OfType i _) = i
        metaId (JustType i) = i
        metaId (JustSort i) = i
        metaId (Assign i e) = i
        metaId _ = __IMPOSSIBLE__
        print' x = do
            r <- getMetaRange $ nmid $ metaId x
            d <- showM x
            liftIO $ putStrLn $ render d ++ "  [ at " ++ prettyShow r ++ " ]"
showMetas _ = liftIO $ putStrLn $ ":meta [metaid]"


showScope :: TCM ()
showScope = do
  scope <- getScope
  liftIO $ putStrLn $ prettyShow scope

metaParseExpr ::  InteractionId -> String -> TCM A.Expr
metaParseExpr ii s =
    do  m <- lookupInteractionId ii
        scope <- getMetaScope <$> lookupLocalMeta m
        r <- getRange <$> lookupLocalMeta m
        -- liftIO $ putStrLn $ prettyShow scope
        let pos = fromMaybe __IMPOSSIBLE__ (rStart r)
        (e, attrs) <- runPM $ parsePosString exprParser pos s
        checkAttributes attrs
        concreteToAbstract scope e

actOnMeta :: [String] -> (InteractionId -> A.Expr -> TCM a) -> TCM a
actOnMeta (is:es) f =
     do  i <- readM is
         let ii = InteractionId i
         e <- metaParseExpr ii (unwords es)
         withInteractionId ii $ f ii e
actOnMeta _ _ = __IMPOSSIBLE__


giveMeta :: [String] -> TCM ()
giveMeta s | length s >= 2 = do
  _ <- actOnMeta s $ \ ii e -> give WithoutForce ii Nothing e
  return ()
giveMeta _ = liftIO $ putStrLn $ ": give" ++ " metaid expr"



refineMeta :: [String] -> TCM ()
refineMeta s | length s >= 2 = do
  _ <- actOnMeta s $ \ ii e -> refine WithoutForce ii Nothing e
  return ()
refineMeta _ = liftIO $ putStrLn $ ": refine" ++ " metaid expr"



retryConstraints :: TCM ()
retryConstraints = wakeupConstraints_


evalIn :: [String] -> TCM ()
evalIn s | length s >= 2 =
    do  d <- actOnMeta s $ \_ e -> prettyA =<< evalInCurrent DefaultCompute e
        liftIO $ print d
evalIn _ = liftIO $ putStrLn ":eval metaid expr"

parseExpr :: String -> TCM A.Expr
parseExpr s = do
    (e, attrs) <- runPM $ parse exprParser s
    checkAttributes attrs
    localToAbstract e return

evalTerm :: String -> TCM (ExitCode a)
evalTerm s =
    do  e <- parseExpr s
        v <- evalInCurrent DefaultCompute e
        e <- prettyTCM v
        liftIO $ print e
        return Continue

typeOf :: [String] -> TCM ()
typeOf s =
    do  e  <- parseExpr (unwords s)
        e0 <- typeInCurrent Normalised e
        e1 <- typeInCurrent AsIs e
        liftIO . putStrLn =<< showA e1

typeIn :: [String] -> TCM ()
typeIn s@(_:_:_) =
    actOnMeta s $ \i e ->
    do  e1 <- typeInMeta i Normalised e
        e2 <- typeInMeta i AsIs e
        liftIO . putStrLn =<< showA e1
typeIn _ = liftIO $ putStrLn ":typeIn meta expr"

showContext :: [String] -> TCM ()
showContext (meta:args) = do
    i <- InteractionId <$> readM meta
    mi <- lookupLocalMeta =<< lookupInteractionId i
    withMetaInfo (getMetaInfo mi) $ do
      ctx <- List.map I.unDom . telToList <$> getContextTelescope
      zipWithM_ display ctx $ reverse $ zipWith const [1..] ctx
    where
        display (x, t) n = do
            t <- case args of
                    ["normal"] -> normalise $ raise n t
                    _          -> return $ raise n t
            d <- prettyTCM t
            liftIO $ print $ text (argNameToString x) <+> ":" <+> d
showContext _ = liftIO $ putStrLn ":Context meta"

-- | The logo that prints when Agda is started in interactive mode.
splashScreen :: String
splashScreen = unlines
    [ "                 _ "
    , "   ____         | |"
    , "  / __ \\        | |"
    , " | |__| |___  __| | ___"
    , " |  __  / _ \\/ _  |/ __\\     Agda Interactive"
    , " | |  |/ /_\\ \\/_| / /_| \\"
    , " |_|  |\\___  /____\\_____/    Type :? for help."
    , "        __/ /"
    , "        \\__/"
    , ""
    -- , "The interactive mode is no longer supported. Don't complain if it doesn't work."
    , "The interactive mode is no longer under active development. Use at your own risk."
    ]

-- | The help message
help :: [Command a] -> IO ()
help cs = putStr $ unlines $
    [ "Command overview" ] ++ List.map explain cs ++
    [ "<exp> Infer type of expression <exp> and evaluate it." ]
    where
        explain (x,_) = ":" ++ x

-- Read -------------------------------------------------------------------

readM :: Read a => String -> TCM a
readM s = maybe err return $ readMaybe s
  where
  err    = throwError $ strMsg $ "Cannot parse: " ++ s
  strMsg = Exception noRange . text
