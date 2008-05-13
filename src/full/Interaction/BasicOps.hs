{-# OPTIONS -cpp -fglasgow-exts -fallow-undecidable-instances #-}

module Interaction.BasicOps where
{- TODO: The operations in this module should return Expr and not String, 
         for this we need to write a translator from Internal to Abstract syntax.
-}


import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List

import Interaction.Monad 

import qualified Syntax.Concrete as C -- ToDo: Remove with instance of ToConcrete
import Syntax.Position
import Syntax.Abstract 
import Syntax.Common
import Syntax.Info(ExprInfo(..),MetaInfo(..))
import Syntax.Internal (MetaId(..),Type(..),Term(..),Sort)
import Syntax.Translation.InternalToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Translation.ConcreteToAbstract
import Syntax.Scope.Base
import Syntax.Fixity(Precedence(..))
import Syntax.Parser

import TypeChecker
import TypeChecking.Conversion
import TypeChecking.Monad as M
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute

import Utils.Monad
import Utils.Monad.Undo

#include "../undefined.h"

parseExprIn :: InteractionId -> Range -> String -> TCM Expr
parseExprIn ii rng s = do
    mId <- lookupInteractionId ii
    updateMetaVarRange mId rng       
    mi  <- getMetaInfo <$> lookupMeta mId
    e <- liftIO $ parsePosString exprParser (rStart (getRange mi)) s
    concreteToAbstract (clScope mi) e

giveExpr :: MetaId -> Expr -> IM Expr
-- When translater from internal to abstract is given, this function might return
-- the expression returned by the type checker.
giveExpr mi e = 
    do  mv <- lookupMeta mi 
        withMetaInfo (getMetaInfo mv) $ metaTypeCheck' mi e mv
        
  where  metaTypeCheck' mi e mv = 
            case mvJudgement mv of 
		 HasType _ t  -> do
		    ctx <- getContextArgs
		    let t' = t `piApply` ctx
		    v	<- checkExpr e t'
		    case mvInstantiation mv of
			InstV v' ->
			    addConstraints =<< equalTerm t' v (v' `apply` ctx)
			_	 -> updateMeta mi v
		    reify v
		 IsSort _ -> __IMPOSSIBLE__

give :: InteractionId -> Maybe Range -> Expr -> IM (Expr,[InteractionId])
give ii mr e = liftTCM $  
     do  setUndo
         mi <- lookupInteractionId ii 
         mis <- getInteractionPoints
         r <- getInteractionRange ii
         updateMetaVarRange mi $ maybe r id mr
         giveExpr mi e
         removeInteractionPoint ii 
         mis' <- getInteractionPoints
         return (e, mis' \\ mis) 


addDecl :: Declaration -> TCM ([InteractionId])
addDecl d = 
    do   setUndo
         mis <- getInteractionPoints
         checkDecl d
         mis' <- getInteractionPoints
         return (mis' \\ mis) 


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
                      let metaVar = QuestionMark
				  $ Syntax.Info.MetaInfo
				    { Syntax.Info.metaRange = r
                                    , Syntax.Info.metaScope = scope { scopePrecedence = ArgumentCtx }
				    , metaNumber = Nothing
				    }
                      in App (ExprRange $ r) e (Arg NotHidden $ unnamed metaVar)
                 --ToDo: The position of metaVar is not correct
                 --ToDo: The fixity of metavars is not correct -- fixed? MT

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


data OutputForm a b
      = OfType b a | EqInType a b b
      | JustType b | EqTypes b b
      | JustSort b | EqSorts b b
      | Guard (OutputForm a b) [OutputForm a b]
      | Assign b a

outputFormId :: OutputForm a b -> b
outputFormId o = case o of
  OfType i _	 -> i
  EqInType _ i _ -> i
  JustType i	 -> i
  EqTypes i _	 -> i
  JustSort i	 -> i
  EqSorts i _	 -> i
  Guard o _	 -> outputFormId o
  Assign i _	 -> i

instance Functor (OutputForm a) where
    fmap f (OfType e t) = OfType (f e) t
    fmap f (JustType e) = JustType (f e)
    fmap f (JustSort e) = JustSort (f e)
    fmap f (EqInType t e e') = EqInType t (f e) (f e')
    fmap f (EqTypes e e') = EqTypes (f e) (f e')
    fmap f (EqSorts e e') = EqSorts (f e) (f e')
    fmap f (Guard o os)	= Guard (fmap f o) (fmap (fmap f) os)
    fmap f (Assign m e) = Assign (f m) e

instance Reify Constraint (OutputForm Expr Expr) where
    reify (ValueEq t u v) = EqInType <$> reify t <*> reify u <*> reify v 
    reify (TypeEq t t') = EqTypes <$> reify t <*> reify t'
    reify (SortEq s s') = EqSorts <$> reify s <*> reify s'
    reify (Guarded c cs) = do
	o  <- reify c
	os <- mapM (withConstraint reify) cs
	return $ Guard o os
    reify (UnBlock m) = do
        mi <- mvInstantiation <$> lookupMeta m
        case mi of
          BlockedConst t -> do
            e  <- reify t
            m' <- reify (MetaV m [])
            return $ Assign m' e
          PostponedTypeCheckingProblem cl -> enterClosure cl $ \(e, a, _) -> do
            a <- reify a
            return $ OfType e a
          Open{}  -> __IMPOSSIBLE__
          InstS{} -> __IMPOSSIBLE__
          InstV{} -> __IMPOSSIBLE__

instance (Show a,Show b) => Show (OutputForm a b) where
    show (OfType e t) = show e ++ " : " ++ show t
    show (JustType e) = "Type " ++ show e
    show (JustSort e) = "Sort " ++ show e
    show (EqInType t e e') = show e ++ " = " ++ show e' ++ " : " ++ show t
    show (EqTypes  t t') = show t ++ " = " ++ show t'
    show (EqSorts s s') = show s ++ " = " ++ show s'
    show (Guard o os)	= show o ++ "  |  " ++ show os
    show (Assign m e) = show m ++ " := " ++ show e

instance (ToConcrete a c, ToConcrete b d) => 
         ToConcrete (OutputForm a b) (OutputForm c d) where
    toConcrete (OfType e t) = OfType <$> toConcrete e <*> toConcrete t
    toConcrete (JustType e) = JustType <$> toConcrete e
    toConcrete (JustSort e) = JustSort <$> toConcrete e
    toConcrete (EqInType t e e') = 
             EqInType <$> toConcrete t <*> toConcrete e <*> toConcrete e'
    toConcrete (EqTypes e e') = EqTypes <$> toConcrete e <*> toConcrete e'
    toConcrete (EqSorts e e') = EqSorts <$> toConcrete e <*> toConcrete e'
    toConcrete (Guard o os) = Guard <$> toConcrete o <*> toConcrete os
    toConcrete (Assign m e) = Assign <$> toConcrete m <*> toConcrete e

--ToDo: Move somewhere else
instance ToConcrete InteractionId C.Expr where
    toConcrete (InteractionId i) = return $ C.QuestionMark noRange (Just i)
instance ToConcrete MetaId C.Expr where
    toConcrete (MetaId i) = return $ C.Underscore noRange (Just i)

judgToOutputForm :: Judgement a c -> OutputForm a c
judgToOutputForm (HasType e t) = OfType e t
judgToOutputForm (IsSort s)    = JustSort s


mkUndo :: IM ()
mkUndo = undo

--- Printing Operations
getConstraint :: Int -> IM (OutputForm Expr Expr)
getConstraint ci = 
    do  cc <- lookupConstraint ci 
        cc <- reduce cc
        withConstraint reify cc


getConstraints :: IM [OutputForm Expr Expr] 
getConstraints = liftTCM $
    do	cs <- M.getConstraints
	cs <- reduce cs
	mapM (withConstraint reify) cs

typeOfMetaMI :: Rewrite -> MetaId -> IM (OutputForm Expr MetaId)
typeOfMetaMI norm mi = 
     do mv <- lookupMeta mi
	withMetaInfo (getMetaInfo mv) $
	  rewriteJudg mv (mvJudgement mv)
   where
    rewriteJudg mv (HasType i t) = 
	withMetaInfo (getMetaInfo mv) $ do
	    t <- rewrite norm t
	    vs <- getContextArgs
	    OfType i <$> reify (t `piApply` vs)
    rewriteJudg mv (IsSort i)    = return $ JustSort i


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
               openAndImplicit is x (MetaVar _ _ _ M.Open _)		 = x `notElem` is
	       openAndImplicit is x (MetaVar _ _ _ (M.BlockedConst _) _) = True
	       openAndImplicit _ _ _					 = False

contextOfMeta :: InteractionId -> Rewrite -> IM [OutputForm Expr Name]
contextOfMeta ii norm = do
  info <- getMetaInfo <$> (lookupMeta =<< lookupInteractionId ii)
  let localVars = map ctxEntry . envContext . clEnv $ info
  withMetaInfo info $ filter visible <$> reifyContext localVars
  where visible (OfType x _) = show x /= "_"
	visible _	     = __IMPOSSIBLE__
        reifyContext xs = escapeContext (length xs) $ foldr out (return []) $ reverse xs
	out (Arg h (x,t)) rest = do
	  t' <- reify =<< rewrite norm t
	  ts <- addCtx x (Arg h t) rest
	  return $ OfType x t' : ts


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

withInteractionId :: InteractionId -> TCM a -> TCM a
withInteractionId i ret = do
  m <- lookupInteractionId i
  withMetaId m ret

withMetaId :: MetaId -> TCM a -> TCM a
withMetaId m ret = do
  info <- lookupMeta m
  withMetaInfo (mvInfo info) ret

-------------------------------
----- Help Functions ----------
-------------------------------





