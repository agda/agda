{-# OPTIONS -cpp -fglasgow-exts #-}

module Interaction.CommandLine.CommandLine where

import Prelude hiding (print, putStr, putStrLn)
import Utils.IO

import Control.Monad.Error
import Control.Monad.Reader
import Data.Char
import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Data.Maybe

import Interaction.BasicOps as BasicOps
import Interaction.Monad

import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Parser
import Syntax.Position
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.InternalToAbstract
import Syntax.Abstract.Pretty

import Text.PrettyPrint

import TypeChecker
import TypeChecking.Conversion
import TypeChecking.Constraints
import TypeChecking.Monad
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Errors

import Utils.ReadLine
import Utils.Monad
import Utils.Fresh
import Utils.Monad.Undo

#include "../../undefined.h"

data ExitCode a = Continue | ContinueIn TCEnv | Return a

type Command a = (String, [String] -> IM (ExitCode a))

matchCommand :: String -> [Command a] -> Either [String] ([String] -> IM (ExitCode a))
matchCommand x cmds =
    case List.filter (isPrefixOf x . fst) cmds of
	[(_,m)]	-> Right m
	xs	-> Left $ List.map fst xs

interaction :: String -> [Command a] -> (String -> IM (ExitCode a)) -> IM a
interaction prompt cmds eval = loop
    where
	go (Return x)	    = return x
	go Continue	    = loop
	go (ContinueIn env) = local (const env) loop

	loop =
	    do	ms <- liftIO $ readline prompt
		case fmap words ms of
		    Nothing		  -> return $ error "** EOF **"
		    Just []		  -> loop
		    Just ((':':cmd):args) ->
			do  liftIO $ addHistory (fromJust ms)
			    case matchCommand cmd cmds of
				Right c	-> go =<< c args
				Left []	->
				    do	liftIO $ putStrLn $ "Unknown command '" ++ cmd ++ "'"
					loop
				Left xs	->
				    do	liftIO $ putStrLn $ "More than one command match: " ++ concat (intersperse ", " xs)
					loop
		    Just _ ->
			do  liftIO $ addHistory (fromJust ms)
			    go =<< eval (fromJust ms)
	    `catchError` \e ->
		do  s <- prettyError e
		    liftIO $ putStrLn s
		    loop

-- | The interaction loop.
interactionLoop :: IM () -> IM ()
interactionLoop typeCheck =
    do  reload
	interaction "Main> " commands evalTerm
    where
	reload = (setUndo >> typeCheck) `catchError` \e -> do
		    s <- prettyError e
		    liftIO $ putStrLn s
		    liftIO $ putStrLn "Failed."

	commands =
	    [ "quit"	    |>  \_ -> return $ Return ()
	    , "?"	    |>  \_ -> continueAfter $ liftIO $ help commands
	    , "reload"	    |>  \_ -> do reload
					 ContinueIn <$> ask
	    , "constraints" |> \args -> continueAfter $ showConstraints args
            , "give"	    |> \args -> continueAfter $ giveMeta args
            , "refine"	    |> \args -> continueAfter $ refineMeta args
	    , "meta"	    |> \args -> continueAfter $ showMetas args
            , "undo"	    |> \_ -> continueAfter $ mkUndo
            , "load"	    |> \args -> continueAfter $ loadFile reload args
	    , "eval"	    |> \args -> continueAfter $ evalIn args
            , "typeOf"      |> \args -> continueAfter $ typeOf args
            , "typeIn"      |> \args -> continueAfter $ typeIn args
	    , "wakeup"	    |> \_ -> continueAfter $ retryConstraints
	    ]
	    where
		(|>) = (,)

continueAfter :: IM a -> IM (ExitCode b)
continueAfter m = m >> return Continue

loadFile :: IM () -> [String] -> IM ()
loadFile reload [file] =
    do	setInputFile file
	reload
loadFile _ _ = liftIO $ putStrLn ":load file"

showConstraints :: [String] -> IM ()
showConstraints [c] =
    do	i  <- readM c
	cc <- normalise =<< lookupConstraint (CId i)
	liftIO $ print $ clValue cc
showConstraints [] =
    do	cs <- BasicOps.getConstraints
	liftIO $ putStrLn $ unlines $ List.map show cs
showConstraints _ = liftIO $ putStrLn ":constraints [cid]"

	
showMetas :: [String] -> IM ()
showMetas [m] =
    do	i <- readM m
	s <- typeOfMeta AsIs (InteractionId i)
	liftIO $ putStrLn $ show s
showMetas [m,"normal"] =
    do	i <- readM m
	s <- typeOfMeta Normalised (InteractionId i)
	liftIO $ putStrLn $ show s
showMetas [] = 
    do  (interactionMetas,hiddenMetas) <- typeOfMetas AsIs 
        let ims =  List.map show interactionMetas 
            hms =  List.map show hiddenMetas
        liftIO $ putStrLn $ unlines $ ims ++ hms
showMetas _ = liftIO $ putStrLn $ ":meta [metaid]"



metaParseExpr ::  InteractionId -> String -> IM A.Expr
metaParseExpr ii s = 
    do	m <- lookupInteractionId ii
        i <- fresh
        scope <- getMetaScope <$> lookupMeta m
        r <- getRange <$> lookupMeta m
        --liftIO $ putStrLn $ show scope
	let ss = ScopeState { freshId = i }
	liftIO $ concreteToAbstract ss scope (c r)
    where
	c r = parsePosString exprParser (rStart r) s

actOnMeta :: [String] -> (InteractionId -> A.Expr -> IM a) -> IM a
actOnMeta (is:es) f = 
     do  i <- readM is
         let ii = InteractionId i 
         e <- metaParseExpr ii (unwords es)
         f ii e
actOnMeta _ _ = __IMPOSSIBLE__


giveMeta :: [String] -> IM ()
giveMeta s | length s >= 2 = 
    do  actOnMeta s (\ii -> \e  -> give ii Nothing e)
        return ()
giveMeta _ = liftIO $ putStrLn $ ": give" ++ " metaid expr"



refineMeta :: [String] -> IM ()
refineMeta s | length s >= 2 = 
    do  actOnMeta s (\ii -> \e  -> refine ii Nothing e)
        return ()
refineMeta _ = liftIO $ putStrLn $ ": refine" ++ " metaid expr"



retryConstraints :: IM ()
retryConstraints = liftTCM wakeupConstraints


evalIn :: [String] -> TCM ()
evalIn s | length s >= 2 =
    do	v <- actOnMeta s evalInMeta
        liftIO $ putStrLn $ show v
evalIn _ = liftIO $ putStrLn ":eval metaid expr"

parseExpr :: String -> TCM A.Expr
parseExpr s =
    do	i <- fresh
	scope <- getScope
	let ss = ScopeState { freshId = i }
	liftIO $ concreteToAbstract ss scope c
    where
	c = parse exprParser s

-- evalTerm :: String -> TCM ()
evalTerm s =
    do	e <- parseExpr s
        v <- evalInCurrent e
	e <- reify v
	liftIO $ putStrLn $ showA e
	return Continue
    where
	evalInCurrent e = 
	    do  t <- newTypeMeta_ 
		v <- checkExpr e t
		v' <- normalise v
		return v'


typeOf :: [String] -> TCM ()
typeOf s = 
    do  e  <- parseExpr (unwords s)
        e0 <- typeInCurrent Normalised e
        e1 <- typeInCurrent AsIs e
	liftIO $ putStrLn $ showA e0

typeIn :: [String] -> TCM ()
typeIn s@(_:_:_) = 
    actOnMeta s $ \i e ->
    do	e1  <- typeInMeta i Normalised e
        e2 <- typeInMeta i AsIs e
	liftIO $ putStrLn $ showA e1
typeIn _ = liftIO $ putStrLn ":typeIn meta expr"



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
    ]

-- | The help message
help :: [Command a] -> IO ()
help cs = putStr $ unlines $
    [ "Command overview" ] ++ List.map explain cs ++
    [ "<exp> Infer type of expression <exp> and evaluate it." ]
    where
	explain (x,_) = ":" ++ x

