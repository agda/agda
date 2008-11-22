{-# LANGUAGE CPP #-}

module Agda.Interaction.CommandLine.CommandLine where

import Prelude hiding (print, putStr, putStrLn)
import Agda.Utils.IO

import Control.Monad.Error
import Control.Monad.Reader
import Control.Applicative
import Data.Char
import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Data.Maybe

import Agda.Interaction.BasicOps as BasicOps
import Agda.Interaction.Monad

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Abstract.Pretty

import Text.PrettyPrint

import Agda.TypeChecker
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Monad
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Substitute

import Agda.Termination.Dumb(checkTermination)

import Agda.Utils.Monad
import Agda.Utils.Fresh
import Agda.Utils.Monad.Undo

#include "../../undefined.h"
import Agda.Utils.Impossible

data ExitCode a = Continue | ContinueIn TCEnv | Return a

type Command a = (String, [String] -> TCM (ExitCode a))

matchCommand :: String -> [Command a] -> Either [String] ([String] -> TCM (ExitCode a))
matchCommand x cmds =
    case List.filter (isPrefixOf x . fst) cmds of
	[(_,m)]	-> Right m
	xs	-> Left $ List.map fst xs

interaction :: String -> [Command a] -> (String -> TCM (ExitCode a)) -> IM a
interaction prompt cmds eval = loop
    where
	go (Return x)	    = return x
	go Continue	    = loop
	go (ContinueIn env) = local (const env) loop

	loop =
	    do	ms <- readline prompt
		case fmap words ms of
		    Nothing		  -> return $ error "** EOF **"
		    Just []		  -> loop
		    Just ((':':cmd):args) ->
			do  case matchCommand cmd cmds of
				Right c	-> go =<< liftTCM (c args)
				Left []	->
				    do	liftIO $ putStrLn $ "Unknown command '" ++ cmd ++ "'"
					loop
				Left xs	->
				    do	liftIO $ putStrLn $ "More than one command match: " ++ concat (intersperse ", " xs)
					loop
		    Just _ ->
			do  go =<< liftTCM (eval $ fromJust ms)
	    `catchError` \e ->
		do  s <- prettyError e
		    liftIO $ putStrLn s
		    loop

-- | The interaction loop.
interactionLoop :: TCM (ScopeInfo, a) -> IM ()
interactionLoop typeCheck =
    do  liftTCM reload
	interaction "Main> " commands evalTerm
    where
	reload = do
	    setUndo
	    (scope, a) <- typeCheck
	    setScope scope
	  `catchError` \e -> do
	    s <- prettyError e
	    liftIO $ putStrLn s
	    liftIO $ putStrLn "Failed."

	commands =
	    [ "quit"	    |>  \_ -> return $ Return ()
	    , "?"	    |>  \_ -> continueAfter $ liftIO $ help commands
	    , "reload"	    |>  \_ -> do reload
					 ContinueIn <$> ask
	    , "constraints" |> \args -> continueAfter $ showConstraints args
	    , "Context"	    |> \args -> continueAfter $ showContext args
            , "give"	    |> \args -> continueAfter $ giveMeta args
            , "Refine"	    |> \args -> continueAfter $ refineMeta args
	    , "metas"	    |> \args -> continueAfter $ showMetas args
            , "undo"	    |> \_ -> continueAfter $ mkUndo
            , "load"	    |> \args -> continueAfter $ loadFile reload args
	    , "eval"	    |> \args -> continueAfter $ evalIn args
            , "typeOf"      |> \args -> continueAfter $ typeOf args
            , "typeIn"      |> \args -> continueAfter $ typeIn args
	    , "wakeup"	    |> \_ -> continueAfter $ retryConstraints
	    , "termination" |> \_ -> continueAfter $ checkTermination 
	    , "noundo"	    |> \_ -> continueAfter $ clearUndoHistory
	    , "scope"	    |> \_ -> continueAfter $ showScope
	    ]
	    where
		(|>) = (,)

continueAfter :: TCM a -> TCM (ExitCode b)
continueAfter m = m >> return Continue

loadFile :: TCM () -> [String] -> TCM ()
loadFile reload [file] =
    do	setInputFile file
	reload
loadFile _ _ = liftIO $ putStrLn ":load file"

showConstraints :: [String] -> TCM ()
showConstraints [c] =
    do	i  <- readM c
	cc <- normalise =<< lookupConstraint i
	d  <- prettyTCM $ clValue cc
	liftIO $ print d
showConstraints [] =
    do	cs <- BasicOps.getConstraints
	ds <- mapM showA cs
	liftIO $ putStrLn $ unlines ds
showConstraints _ = liftIO $ putStrLn ":constraints [cid]"

	
showMetas :: [String] -> TCM ()
showMetas [m] =
    do	i <- InteractionId <$> readM m
	withInteractionId i $ do
	  s <- typeOfMeta AsIs i
	  r <- getInteractionRange i
	  d <- showA s
	  liftIO $ putStrLn $ d ++ " " ++ show r
showMetas [m,"normal"] =
    do	i <- InteractionId <$> readM m
	withInteractionId i $ do
	  s <- showA =<< typeOfMeta Normalised i
	  r <- getInteractionRange i
	  liftIO $ putStrLn $ s ++ " " ++ show r
showMetas [] = 
    do  (interactionMetas,hiddenMetas) <- typeOfMetas AsIs 
        mapM_ (liftIO . putStrLn) =<< mapM showII interactionMetas
	mapM_ print' hiddenMetas
    where
	showII o = withInteractionId (outputFormId o) $ showA o
	showM  o = withMetaId (outputFormId o) $ showA o

	metaId (OfType i _) = i
	metaId (JustType i) = i
	metaId (JustSort i) = i
	metaId (Assign i e) = i
	metaId _ = __IMPOSSIBLE__
	print' x = do
	    r <- getMetaRange (metaId x)
	    d <- showM x
	    liftIO $ putStrLn $ d ++ "  [ at " ++ show r ++ " ]"
showMetas _ = liftIO $ putStrLn $ ":meta [metaid]"


showScope :: TCM ()
showScope = do
  scope <- getScope
  liftIO $ print scope

metaParseExpr ::  InteractionId -> String -> TCM A.Expr
metaParseExpr ii s = 
    do	m <- lookupInteractionId ii
        scope <- getMetaScope <$> lookupMeta m
        r <- getRange <$> lookupMeta m
        --liftIO $ putStrLn $ show scope
        let pos = case rStart r of
                    Nothing  -> __IMPOSSIBLE__
                    Just pos -> pos
	e <- liftIO $ parsePosString exprParser pos s
	concreteToAbstract scope e

actOnMeta :: [String] -> (InteractionId -> A.Expr -> TCM a) -> TCM a
actOnMeta (is:es) f = 
     do  i <- readM is
         let ii = InteractionId i 
         e <- metaParseExpr ii (unwords es)
         withInteractionId ii $ f ii e
actOnMeta _ _ = __IMPOSSIBLE__


giveMeta :: [String] -> TCM ()
giveMeta s | length s >= 2 = 
    do  actOnMeta s (\ii -> \e  -> give ii Nothing e)
        return ()
giveMeta _ = liftIO $ putStrLn $ ": give" ++ " metaid expr"



refineMeta :: [String] -> TCM ()
refineMeta s | length s >= 2 = 
    do  actOnMeta s (\ii -> \e  -> refine ii Nothing e)
        return ()
refineMeta _ = liftIO $ putStrLn $ ": refine" ++ " metaid expr"



retryConstraints :: TCM ()
retryConstraints = liftTCM wakeupConstraints


evalIn :: [String] -> TCM ()
evalIn s | length s >= 2 =
    do	d <- actOnMeta s $ \_ e -> prettyA =<< evalInCurrent e
        liftIO $ print d
evalIn _ = liftIO $ putStrLn ":eval metaid expr"

parseExpr :: String -> TCM A.Expr
parseExpr s = do
    e <- liftIO $ parse exprParser s
    localToAbstract e return

evalTerm :: String -> TCM (ExitCode a)
evalTerm s =
    do	e <- parseExpr s
        v <- evalInCurrent e
	e <- prettyTCM v
	liftIO $ putStrLn $ show e
	return Continue
    where
	evalInCurrent e = do
	  t <- newTypeMeta_ 
	  v <- checkExpr e t
	  v' <- normalise v
	  return v'


typeOf :: [String] -> TCM ()
typeOf s = 
    do  e  <- parseExpr (unwords s)
        e0 <- typeInCurrent Normalised e
        e1 <- typeInCurrent AsIs e
	liftIO . putStrLn =<< showA e1

typeIn :: [String] -> TCM ()
typeIn s@(_:_:_) = 
    actOnMeta s $ \i e ->
    do	e1  <- typeInMeta i Normalised e
        e2 <- typeInMeta i AsIs e
	liftIO . putStrLn =<< showA e1
typeIn _ = liftIO $ putStrLn ":typeIn meta expr"

showContext :: [String] -> TCM ()
showContext (meta:args) = do
    i <- InteractionId <$> readM meta
    mi <- lookupMeta =<< lookupInteractionId i
    withMetaInfo (getMetaInfo mi) $ do
    ctx <- List.map unArg . telToList <$> getContextTelescope
    zipWithM_ display ctx $ reverse $ zipWith const [1..] ctx
    where
	display (x, t) n = do
	    t <- case args of
		    ["normal"] -> normalise $ raise n t
		    _	       -> return $ raise n t
	    d <- prettyTCM t
	    liftIO $ print $ text x <+> text ":" <+> d
showContext _ = liftIO $ putStrLn ":Context meta"

-- | The logo that prints when agdaLight is started in interactive mode.
splashScreen :: String
splashScreen = unlines
    [ "                 _        ______"
    , "   ____         | |      |_ __ _|"
    , "  / __ \\        | |       | || |"
    , " | |__| |___  __| | ___   | || |"
    , " |  __  / _ \\/ _  |/ __\\  | || |   Agda 2 Interactive"
    , " | |  |/ /_\\ \\/_| / /_| \\ | || |"
    , " |_|  |\\___  /____\\_____/|______|  Type :? for help."
    , "        __/ /"
    , "        \\__/"
    , ""
    , "The interactive mode is no longer supported. Don't complain if it doesn't work."
    ]

-- | The help message
help :: [Command a] -> IO ()
help cs = putStr $ unlines $
    [ "Command overview" ] ++ List.map explain cs ++
    [ "<exp> Infer type of expression <exp> and evaluate it." ]
    where
	explain (x,_) = ":" ++ x

