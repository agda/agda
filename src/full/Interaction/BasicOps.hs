{-# OPTIONS -cpp -fglasgow-exts #-}

module Interaction.BasicOps where

--import Prelude hiding (print, putStr, putStrLn)
--import Utils.IO

--import Control.Monad.Error
--import Control.Monad.Reader
--import Data.Char
--import Data.Set as Set
--import Data.Map as Map
--import Data.List as List
--import Data.Maybe
--import Text.PrettyPrint

--import Syntax.Position
--import Syntax.Abstract
--import Syntax.Translation.ConcreteToAbstract
--import Syntax.Parser
--import Syntax.Scope

--import TypeChecker
--import TypeChecking.Monad
--import TypeChecking.Monad.Context
--import TypeChecking.MetaVars
--import TypeChecking.Reduce

--import Utils.ReadLine
--import Utils.Monad
--import Utils.Fresh




showConstraints :: IM Constraints 
showConstraints =
    do	cs <- getConstraints
	return$ refresh cs


showMetas :: TCM ()
showMetas =
    do	m <- Map.filter interesting <$> getMetaStore
	m <- refresh m
	liftIO $ putStrLn $ unlines $ List.map prm $ Map.assocs m
    where
	prm (x,i) = "?" ++ show x ++ " := " ++ show i

	interesting (HoleV _ _ _)	= True
	interesting (HoleT _ _ _)	= True
	interesting (UnderScoreV _ _ _) = True
	interesting (UnderScoreT _ _ _) = True
	interesting _			= False

parseExpr :: String -> TCM Expr
parseExpr s =
    do	i <- fresh
	scope <- getScope
	let ss = ScopeState { freshId = i }
	liftIO $ concreteToAbstract ss scope c
    where
	c = parse exprParser s

evalTerm s =
    do	e <- parseExpr s
	t <- newTypeMeta_ (getRange e)
	v <- checkExpr e t
	t' <- refresh t
	v' <- refresh v
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

