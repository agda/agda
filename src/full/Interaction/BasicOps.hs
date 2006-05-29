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

import qualified Syntax.Concrete -- ToDo: Remove with instance of ToConcrete
import Syntax.Position
import Syntax.Abstract 
import Syntax.Common
import Syntax.Info(ExprInfo(..),MetaInfo(..))
import Syntax.Internal (MetaId(..),Type,Sort)
import Syntax.Translation.InternalToAbstract
import Syntax.Translation.AbstractToConcrete
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

giveExpr :: MetaId -> Expr -> IM Expr
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
                        reify v
		 IsType _ s ->
		    do	t <- isType e s
			case mvInstantiation mv of
			    InstT t' -> equalTyp () t (t' `apply` vs)
			    _	     -> return ()
			updateMeta mi t
                        reify t 
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
                 --ToDo: The fixity of metavars is not correct

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
evalInCurrent :: Expr -> IM Expr
evalInCurrent e = 
    do  t <- newTypeMeta_ 
	v <- checkExpr e t
	v' <- normalise v
	reify v'


evalInMeta :: InteractionId -> Expr -> IM Expr
evalInMeta ii e = 
   do 	m <- lookupInteractionId ii
	mi <- getMetaInfo <$> lookupMeta m
	withMetaInfo mi $
	    evalInCurrent e


data Rewrite =  AsIs | Instantiated | HeadNormal | Normalised 

--rewrite :: Rewrite -> Term -> TCM Term
rewrite AsIs	     t = return t
rewrite Instantiated t = return t   -- reify does instantiation
rewrite HeadNormal   t = reduce t
rewrite Normalised   t = normalise t


data OutputForm a b =
      OfType b a | JustType b | EqInType a b b | EqTypes b b


instance Functor (OutputForm a) where
    fmap f (OfType e t) = OfType (f e) t
    fmap f (JustType e) = JustType (f e)
    fmap f (EqInType t e e') = EqInType t (f e) (f e')
    fmap f (EqTypes e e') = EqTypes (f e) (f e')

instance Reify Constraint (OutputForm Expr Expr) where
    reify (ValueEq t u v) = EqInType <$> reify t <*> reify u <*> reify v 
    reify (TypeEq t t') = EqTypes <$> reify t <*> reify t'
    reify _ = __IMPOSSIBLE__

instance (Show a,Show b) => Show (OutputForm a b) where
    show (OfType e t) = show e ++ " : " ++ show t
    show (JustType e) = "Type " ++ show e
    show (EqInType t e e') = show e ++ " = " ++ show e' ++ " : " ++ show t
    show (EqTypes  t t') = show t ++ " = " ++ show t'

instance (ToConcrete a c, ToConcrete b d) => 
         ToConcrete (OutputForm a b) (OutputForm c d) where
    toConcrete (OfType e t) = OfType <$> toConcrete e <*> toConcrete t
    toConcrete (JustType e) = JustType <$> toConcrete e
    toConcrete (EqInType t e e') = 
             EqInType <$> toConcrete t <*> toConcrete e <*> toConcrete e'
    toConcrete (EqTypes e e') = EqTypes <$> toConcrete e <*> toConcrete e'

--ToDo: Move somewhere else
instance ToConcrete InteractionId Syntax.Concrete.Expr where
    toConcrete (InteractionId i) = return $ Syntax.Concrete.QuestionMark noRange (Just i)
instance ToConcrete MetaId Syntax.Concrete.Expr where
    toConcrete (MetaId i) = return $ Syntax.Concrete.QuestionMark noRange (Just i)

judgToOutputForm :: Judgement a b c -> OutputForm a c
judgToOutputForm (HasType e t) = OfType e t
judgToOutputForm (IsType t s) = JustType t
judgToOutputForm _            = __IMPOSSIBLE__


mkUndo :: IM ()
mkUndo = undo

--- Printing Operations
getConstraints :: IM [OutputForm Expr Expr] 
getConstraints = liftTCM $
    do	cs <- Context.getConstraints
	cs <- mapM reduce $ Map.elems cs
        mapM reify $ List.map ccConstraint cs



typeOfMetaMI :: Rewrite -> MetaId -> IM (OutputForm Expr MetaId)
typeOfMetaMI norm mi = 
     do mv <- lookupMeta mi
        let j = mvJudgement mv
        rewriteJudg mv j
   where rewriteJudg mv (HasType i t) = 
             withMetaInfo (getMetaInfo mv) $
                 do  t <- rewrite norm t 
                     OfType i <$> reify t
         rewriteJudg mv (IsType i s)  = return $ JustType i 
         rewriteJudg mv (IsSort i)    = __IMPOSSIBLE__


typeOfMeta :: Rewrite -> InteractionId -> IM (OutputForm Expr InteractionId)
typeOfMeta norm ii = 
     do mi <- lookupInteractionId ii
        out <- typeOfMetaMI norm mi
        return $ fmap (\_ -> ii) out


typeOfMetas :: Rewrite -> IM ([OutputForm Expr InteractionId],[OutputForm Expr MetaId])
-- First visible metas, then hidden
typeOfMetas norm = liftTCM $
    do	ips <- getInteractionPoints 
        js <- mapM (typeOfMeta norm) ips
        hidden <- hiddenMetas
        return $ (js,hidden)
   where hiddenMetas =    --TODO: Change so that it uses getMetaMI above 
            do is <- getInteractionMetas
	       store <- Map.filterWithKey (openAndImplicit is) <$> getMetaStore
               let mvs = Map.keys store
               mapM (typeOfMetaMI norm) mvs
          where
               openAndImplicit is x (MetaVar _ _ M.Open) = x `notElem` is
	       openAndImplicit _ _ _			 = False

contextOfMeta :: InteractionId -> IM [OutputForm Expr Name]
contextOfMeta ii =
     do  mi <- lookupInteractionId ii
         env <- getMetaEnv <$> lookupMeta mi
         let localVars =  List.filter visibleVar $ envContext env
         mapM translate localVars
  where visibleVar (x,_) = (show x) /= "_"
        translate (x,t) = OfType x <$> reify t


{-| Returns the type of the expression in the current environment -}
typeInCurrent :: Rewrite -> Expr -> TCM Expr
typeInCurrent norm e =
    do 	(_,t) <- inferExpr e
        v <- rewrite norm t
        reify v



typeInMeta :: InteractionId -> Rewrite -> Expr -> TCM Expr
typeInMeta ii norm e =
   do 	m <- lookupInteractionId ii
	mi <- getMetaInfo <$> lookupMeta m
	withMetaInfo mi $
	    typeInCurrent norm e


-------------------------------
----- Help Functions ----------
-------------------------------





