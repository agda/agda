{-# OPTIONS -cpp -fglasgow-exts #-}

module Interaction.BasicOps where

--import Prelude hiding (print, putStr, putStrLn)
--import Utils.IO

import Control.Monad.Error
import Control.Monad.Reader
--import Data.Char
--import Data.Set as Set
import Data.Map as Map
import Data.List as List
--import Data.Maybe

import Interaction.Monad 
--import Text.PrettyPrint

--import Syntax.Position
import Syntax.Abstract 
import Syntax.Internal (MetaId)
--import Syntax.Translation.ConcreteToAbstract
--import Syntax.Parser
--import Syntax.Scope

import TypeChecker
import TypeChecking.Conversion
import TypeChecking.Monad as M
import TypeChecking.Monad.Context as Context
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute

--import Utils.ReadLine
import Utils.Monad.Undo
--import Utils.Fresh

#include "../undefined.h"

-- TODO: Modify all operations so that they return abstract syntax and not 
-- stringd

give :: InteractionId -> Expr -> IM ([InteractionId])
give ii e = liftTCM $  
     do  setUndo
         mi <- lookupInteractionId ii 
         mis <- getInteractionPoints
         mv <- lookupMeta mi 
         withMetaInfo (getMetaInfo mv) $
		do vs <- allCtxVars
		   metaTypeCheck' mi e mv vs
         removeInteractionPoint ii 
         mis' <- getInteractionPoints
         return ((List.\\) mis' mis) 
  where  metaTypeCheck' mi e mv vs = 
            case mvJudgement mv of 
		 HasType _ t  ->
		    do	v <- checkExpr e t
			case mvInstantiation mv of
			    InstV v' -> equalVal () t v (v' `apply` vs)
			    _	     -> return ()
			updateMeta mi v
		 IsType _ s ->
		    do	t <- isType e s
			case mvInstantiation mv of
			    InstT t' -> equalTyp () t (t' `apply` vs)
			    _	     -> return ()
			updateMeta mi t
		 IsSort _ -> __IMPOSSIBLE__

getConstraints :: IM [String] -- should be changed to Expr something
getConstraints = liftTCM $
    do	cs <- Context.getConstraints
	--cs <- normalise cs
        return $ List.map prc $ Map.assocs cs
    where
	prc (x,(_,ctx,c)) = show x ++ ": " ++ show (List.map fst $ envContext ctx) ++ " |- " ++ show c


getMeta :: InteractionId -> IM String
getMeta ii = 
     do j <- judgementInteractionId ii
        let j' = fmap (\_ -> ii) j
        return $ show j'
        
getMetas :: IM [String]
getMetas = liftTCM $
    do	ips <- getInteractionPoints 
        js <- mapM judgementInteractionId ips
        js' <- zipWithM mkJudg js ips   -- TODO: write nicer
        return $ List.map show js'
   where mkJudg (HasType _ t) ii = 
             do t <- normalise t 
                return $ HasType ii t
         mkJudg (IsType _ s) ii  = return $ IsType ii s
         mkJudg (IsSort _) ii    = return $ IsSort ii


mkUndo :: IM ()
mkUndo = undo


{-
showMeta :: InteractionId -> TCM (Judgement InteractionId String String)
showMeta ii = do
   mi <- lookupInteractionId ii
   mv <-  lookupMeta mi 
   
   

{-
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

-}
-}
