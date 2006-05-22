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
import Text.PrettyPrint

import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Parser
import Syntax.Position
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract



import TypeChecker
import TypeChecking.Conversion
import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.MetaVars
import TypeChecking.Reduce

import Utils.ReadLine
import Utils.Monad
import Utils.Fresh

#include "../../undefined.h"

data ExitCode a = Continue | ContinueIn TCEnv | Return a

type Command a = (String, [String] -> TCM (ExitCode a))

matchCommand :: String -> [Command a] -> Either [String] ([String] -> TCM (ExitCode a))
matchCommand x cmds =
    case List.filter (isPrefixOf x . fst) cmds of
	[(_,m)]	-> Right m
	xs	-> Left $ List.map fst xs

interaction :: String -> [Command a] -> (String -> TCM (ExitCode a)) -> TCM a
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
		do  liftIO $ print e
		    loop

-- | The interaction loop.
interactionLoop :: TCM () -> TCM ()
interactionLoop typeCheck =
    do	reload
	interaction "Main> " commands evalTerm
    where
	reload = typeCheck `catchError`
		    \e -> liftIO $ do print e
				      putStrLn "Failed."

	commands =
	    [ "quit"	|>  \_ -> return $ Return ()
	    , "help"	|>  \_ -> continueAfter $ liftIO $ putStr help
	    , "?"	|>  \_ -> continueAfter $ liftIO $ putStr help
	    , "reload"	|>  \_ -> do reload
				     ContinueIn <$> ask
	    , "constraints" |> \_ -> continueAfter showConstraints
            , "give" |> \args -> continueAfter $ giveMeta args
	    , "meta" |> \args -> continueAfter $ showMetas args
	    ]
	    where
		(|>) = (,)

continueAfter :: TCM a -> TCM (ExitCode b)
continueAfter m = m >> return Continue

showConstraints :: TCM ()
showConstraints =
    do	cs <- getConstraints
	cs <- normalise cs
	liftIO $ putStrLn $ unlines $ List.map prc $ Map.assocs cs
    where
	prc (x,(_,ctx,c)) = show x ++ ": " ++ show (List.map fst $ envContext ctx) ++ " |- " ++ show c

showMetas :: [String] -> TCM ()
showMetas [m] =
    do	i  <- readM m
	mv <- lookupMeta (MetaId i)
	liftIO $ putStrLn $ "?" ++ show i ++ " " ++ show mv
showMetas [] =
    do	m <- Map.filter interesting <$> getMetaStore
	--m <- normalise m
	liftIO $ putStrLn $ unlines $ List.map prm $ Map.assocs m
    where
	prm (x,i) = "?" ++ show x ++ " " ++ show i

	interesting (MetaVar _ _ Open) = True
	interesting _		       = False
showMetas _ = liftIO $ putStrLn $ ":meta [metaid]"



metaParseExpr ::  MetaId -> String -> TCM A.Expr
metaParseExpr m s = 
    do	i <- fresh
        scope <- getMetaScope <$> lookupMeta m
        liftIO $ putStrLn $ show scope
	let ss = ScopeState { freshId = i }
	liftIO $ concreteToAbstract ss scope c
    where
	c = parse exprParser s

giveMeta :: [String] -> TCM ()
giveMeta [is,es] = 
     do  i <- readM is
         let mi = MetaId i 
         e <- metaParseExpr mi es
         mv <- lookupMeta mi 
         withMetaInfo (getMetaInfo mv) $ metaTypeCheck' mi e mv

 where  metaTypeCheck' mi e mv = 
            case mvJudgement mv of 
		 HasType _ t  ->
		    do	v <- checkExpr e t
			case mvInstantiation mv of
			    InstV v' -> equalVal () t v v'
			    _	     -> __IMPOSSIBLE__
			updateMeta mi v
		 IsType _ s ->
		    do	t <- isType e s
			case mvInstantiation mv of
			    InstT t' -> equalTyp () t t'
			    _	     -> __IMPOSSIBLE__
			updateMeta mi t
		 IsSort _ -> __IMPOSSIBLE__

giveMeta _ = liftIO $ putStrLn "give takes a number of a meta and expression"


parseExpr :: String -> TCM A.Expr
parseExpr s =
    do	i <- fresh
	scope <- getScope
	let ss = ScopeState { freshId = i }
	liftIO $ concreteToAbstract ss scope c
    where
	c = parse exprParser s

evalTerm s =
    do	e <- parseExpr s
	t <- newTypeMeta_ 
	v <- checkExpr e t
	t' <- normalise t
	v' <- normalise v
	liftIO $ putStrLn $ show v' ++ " : " ++ show t'
	return Continue

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
help :: String
help = unlines
    [ "Command overview"
    , ":quit         Quit."
    , ":help or :?   Help (this message)."
    , ":reload       Reload input files."
    , "<exp> Infer type of expression <exp> and evaluate it."
    ]

