{-# OPTIONS -cpp -fglasgow-exts #-}

module Interaction.BasicOps where
{- TODO: The operations in this module should return Expr and not String, 
         for this we need to write a translator from Internal to Abstract syntax.
-}


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

import Syntax.Position
import Syntax.Abstract 
import Syntax.Common
import Syntax.Info(ExprInfo(..),MetaInfo(..))
import Syntax.Internal (MetaId,Type,Sort)
--import Syntax.Translation.ConcreteToAbstract
--import Syntax.Parser
import Syntax.Scope

import TypeChecker
import TypeChecking.Conversion
import TypeChecking.Monad as M
import TypeChecking.Monad.Context as Context
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute

--import Utils.ReadLine
import Utils.Monad
import Utils.Monad.Undo

--import Utils.Fresh

#include "../undefined.h"

-- TODO: Modify all operations so that they return abstract syntax and not 
-- stringd

giveExpr :: MetaId -> Expr -> IM ()
-- When translater from internal to abstract is given, this function might return
-- the expression returned by the type checker.
giveExpr mi e = 
    do  mv <- lookupMeta mi 
        withMetaInfo (getMetaInfo mv) $
		do vs <- allCtxVars
		   metaTypeCheck' mi e mv vs
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

give :: InteractionId -> Maybe Range -> Expr -> IM (Expr,[InteractionId])
give ii mr e = liftTCM $  
     do  setUndo
         mi <- lookupInteractionId ii 
         mis <- getInteractionPoints
         r <- getInteractionRange ii
         updateMetaRange mi $ maybe r id mr
         giveExpr mi e
         removeInteractionPoint ii 
         mis' <- getInteractionPoints
         return (e,(List.\\) mis' mis) 


addDecl :: Declaration -> TCM ([InteractionId])
addDecl d = 
    do   setUndo
         mis <- getInteractionPoints
         checkDecl d
         mis' <- getInteractionPoints
         return ((List.\\) mis' mis) 


refine :: InteractionId -> Maybe Range -> Expr -> TCM (Expr,[InteractionId])
-- If constants has a fixed arity, then it might be better to do 
-- exact refinement.
refine ii mr e = 
    do  mi <- lookupInteractionId ii
        mv <- lookupMeta mi 
        let range = maybe (getRange mv) id mr
        let scope = M.getMetaScope mv
        tryRefine 10 range scope e
  where tryRefine :: Int -> Range -> ScopeInfo -> Expr -> TCM (Expr,[InteractionId])
        tryRefine nrOfMetas r scope e = try nrOfMetas e
           where try 0 e = throwError (strMsg "Can not refine")
                 try n e = give ii (Just r) e `catchError` (\_ -> try (n-1) (appMeta e))
                 appMeta :: Expr -> Expr
                 appMeta e = 
                      let metaVar = QuestionMark $ Syntax.Info.MetaInfo {Syntax.Info.metaRange = r,
                                                 Syntax.Info.metaScope = scope
						 , metaNumber = Nothing
						 }
                      in App (ExprRange $ r) e (Arg NotHidden metaVar)
                 --ToDo: The position of metaVar is not correct

{-
refineExact :: InteractionId -> Maybe Range -> Expr -> TCM (Expr,[InteractionId])
refineExact ii mr e = 
    do  mi <- lookupInteractionId ii
        mv <- lookupMeta mi 
        let range = maybe (getRange mv) id mr
        let scope = M.getMetaScope mv
        (_,t) <- withMetaInfo (getMetaInfo mv) $ inferExpr e         
        let arityt = arity t
        
        tryRefine 10 range scope e
  where tryRefine :: Int -> Range -> ScopeInfo -> Expr -> TCM (Expr,[InteractionId])
        tryRefine nrOfMetas r scope e = try nrOfMetas e
           where try 0 e = throwError (strMsg "Can not refine")
                 try n e = give ii (Just r) e `catchError` (\_ -> try (n-1) (appMeta e))
                 appMeta :: Expr -> Expr
                 appMeta e = 
                      let metaVar = QuestionMark $ Syntax.Info.MetaInfo {Syntax.Info.metaRange = r,
                                                 Syntax.Info.metaScope = scope}
                      in App (ExprRange $ r) NotHidden e metaVar    
                 --ToDo: The position of metaVar is not correct





abstract :: InteractionId -> Maybe Range -> TCM (Expr,[InteractionId])
abstract ii mr 


refineExact :: InteractionId -> Expr -> TCM (Expr,[InteractionId])
refineExact ii e = 
    do  
-}


{-| Evaluate the given expression in the current environment -}
evalInCurrent :: Expr -> IM String
evalInCurrent e = 
    do  t <- newTypeMeta_ 
	v <- checkExpr e t
	v' <- normalise v
	return (show v')


evalInMeta :: InteractionId -> Expr -> IM String 
evalInMeta ii e = 
   do 	m <- lookupInteractionId ii
	mi <- getMetaInfo <$> lookupMeta m
	withMetaInfo mi $
	    evalInCurrent e



mkUndo :: IM ()
mkUndo = undo

--- Printing Operations
getConstraints :: IM [String] 
getConstraints = liftTCM $
    do	cs <- Context.getConstraints
	cs <- normalise cs
        return $ List.map prc $ Map.assocs cs
    where
	prc (x,CC _ ctx c) = show x ++ ": " ++ show (List.map fst $ envContext ctx) ++ " |- " ++ show c


typeOfMetaMI :: Normal -> MetaId -> IM (Judgement Type Sort MetaId)
typeOfMetaMI norm mi = 
     do mv <- lookupMeta mi
        normJudg mv $ mvJudgement mv -- TODO: Better name
   where normJudg mv (HasType i t) = 
             do t <- if (doNormalise norm) then 
                          withMetaInfo (getMetaInfo mv) $ normalise t 
                     else return t
                return $ HasType i t
         normJudg mv (IsType i s)  = IsType i <$> normalise s
         normJudg mv (IsSort i)    = return $ IsSort i

typeOfMeta :: Normal -> InteractionId -> IM String  --TODO: 
typeOfMeta norm ii = 
     do mi <- lookupInteractionId ii
        j <- typeOfMetaMI norm mi
        return $ show $ fmap (\_ -> ii) j 

typeOfMetas :: Normal -> IM ([String],[String])
-- First visible metas, then hidden
typeOfMetas norm = liftTCM $
    do	ips <- getInteractionPoints 
        js <- mapM (typeOfMeta norm) ips
        hiddens <- hiddenMetas
        return $ (List.map show js,List.map show hiddens)
   where hiddenMetas :: TCM [Judgement Type Sort MetaId]
         hiddenMetas =    --TODO: Change so that it uses getMetaMI above 
            do store <- Map.filter open <$> getMetaStore
               let mvs = Map.keys store
               mapM (typeOfMetaMI norm) mvs
          where
	       open :: MetaVariable -> Bool
               open (MetaVar _ _ M.Open) = True
	       open _	        	= False

contextOfMeta :: InteractionId -> IM String
contextOfMeta ii =
     do  mi <- lookupInteractionId ii
         env <- getMetaEnv <$> lookupMeta mi
         let localVars = List.map (\(x,t) -> show x ++ " : " ++ show t) $ List.filter visibleVar $ envContext env
--         let constantsInScope =
         return (unlines localVars)
  where visibleVar (x,_) = (show x) /= "_"

data Normal = Normalised | AsIs 

doNormalise Normalised = True
doNormalise AsIs = False



{-| Returns the type of the expression in the current environment -}
typeInCurrent :: Normal -> Expr -> TCM String
typeInCurrent norm e =
    do 	t <- newTypeMeta_ 
	checkExpr e t
        if doNormalise norm then show <$> normalise t else return $ show t


typeInMeta :: InteractionId -> Normal -> Expr -> TCM String
typeInMeta ii norm e =
   do 	m <- lookupInteractionId ii
	mi <- getMetaInfo <$> lookupMeta m
	withMetaInfo mi $
	    typeInCurrent norm e


-------------------------------
----- Help Functions ----------
-------------------------------






