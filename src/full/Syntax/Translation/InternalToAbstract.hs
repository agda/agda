{-# OPTIONS -cpp -fglasgow-exts #-}

{-|
    Translating from internal syntax to abstract syntax. Enables nice
    pretty printing of internal syntax.

    TODO

	- numbers on metas
	- fake dependent functions to independent functions
	- meta parameters
	- shadowing
-}
module Syntax.Translation.InternalToAbstract where

import Control.Monad.State

import Data.FunctorM
import Data.Map as Map
import Data.List as List

import Syntax.Position
import Syntax.Common
import Syntax.Info as Info
import Syntax.Fixity
import Syntax.Abstract as A
import qualified Syntax.Concrete as C
import Syntax.Internal as I
import Syntax.Internal.Debug
import Syntax.Scope

import TypeChecking.Monad as M
import TypeChecking.Reduce

import Utils.Monad
import Utils.Tuple

#include "../../undefined.h"

apps :: (Expr, [Arg Expr]) -> TCM Expr
apps (e, [])		    = return e
apps (e, arg@(Arg Hidden _) : args) =
    do	showImp <- showImplicitArguments
	if showImp then apps (App exprInfo e arg, args)
		   else apps (e, args)
apps (e, arg:args)	    =
    apps (App exprInfo e arg, args)

nameInfo :: Name -> NameInfo
nameInfo x = NameInfo { bindingSite  = getRange x
		      , concreteName = C.QName $ nameConcrete x
		      , nameFixity   = NonAssoc noRange 10
		      , nameAccess   = PublicAccess
		      }

qnameInfo :: QName -> TCM NameInfo
qnameInfo x =
    do	scope <- getScope
	let fx = case resolveName (qnameConcrete x) scope of
		    DefName d -> fixity d
		    _	      -> NonAssoc noRange 10 -- out of scope
	return $ NameInfo
		 { bindingSite  = noRange
		 , concreteName = qnameConcrete x
		 , nameFixity   = fx
		 , nameAccess   = PublicAccess
		 }

exprInfo :: ExprInfo
exprInfo = ExprRange noRange

reifyApp :: Expr -> [Arg Term] -> TCM Expr
reifyApp e vs = curry apps e =<< reify vs

class Reify i a | i -> a where
    reify :: i -> TCM a

instance Reify MetaId Expr where
    reify x@(MetaId n) =
	do  mi  <- getMetaInfo <$> lookupMeta x
	    let mi' = Info.MetaInfo (getRange mi)
				    (M.metaScope mi)
				    (Just n)
	    iis <- List.map (snd /\ fst) . Map.assocs
		    <$> gets stInteractionPoints
	    case List.lookup x iis of
		Just ii@(InteractionId n)
			-> return $ A.QuestionMark $ mi' {metaNumber = Just n}
		Nothing	-> return $ A.Underscore mi'

instance Reify Term Expr where
    reify v =
	do  v <- instantiate v
	    case ignoreBlocking v of
		I.Var n vs   ->
		    do  x  <- nameOfBV n
			reifyApp (A.Var (nameInfo x) x) vs
		I.Def x vs   ->
		    do	i <- qnameInfo x
			reifyApp (A.Def i x) vs
		I.Con x vs   ->
		    do	i <- qnameInfo x
			reifyApp (A.Con i x) vs
		I.Lam b	->
		    do	(x,e) <- reify b
			return $ A.Lam exprInfo (DomainFree NotHidden x) e -- TODO: hiding
		I.Lit l	     -> return $ A.Lit l
		I.MetaV x vs -> apps =<< reify (x,vs)
		I.BlockedV _ -> __IMPOSSIBLE__

instance Reify Type Expr where
    reify t =
	do  t <- instantiate t
	    case t of
		I.El v _     -> reify v
		I.Pi a b     ->
		    do	Arg h a <- reify a
			(x,b)   <- reify b
			return $ A.Pi exprInfo (TypedBinding noRange h [x] a) b
		I.Fun a b    -> uncurry (A.Fun $ exprInfo)
				<$> reify (a,b)
		I.Sort s     -> reify s
		I.MetaT x vs -> apps =<< reify (x,vs)
		I.LamT _     -> __IMPOSSIBLE__

instance Reify Sort Expr where
    reify s =
	do  s <- normalise s
	    case s of
		I.Type n  -> return $ A.Set exprInfo n
		I.Prop	  -> return $ A.Prop exprInfo
		I.MetaS x -> reify x
		I.Suc s	  ->
		    do	suc <- freshName_ "suc"	-- TODO: hack
			e   <- reify s
			return $ A.App exprInfo (A.Var (nameInfo suc) suc) (Arg NotHidden e)
		I.Lub s1 s2 ->
		    do	lub <- freshName_ "\\/"	-- TODO: hack
			(e1,e2) <- reify (s1,s2)
			let app x y = A.App exprInfo x (Arg NotHidden y)
			return $ A.Var (nameInfo lub) lub `app` e1 `app` e2

instance Reify i a => Reify (Abs i) (Name, a) where
    reify (Abs s v) =
	do  x <- freshName_ s
	    e <- addCtx x __IMPOSSIBLE__ -- type doesn't matter
		 $ reify v
	    return (x,e)

instance Reify i a => Reify (Arg i) (Arg a) where
    reify = fmapM reify

instance Reify i a => Reify [i] [a] where
    reify = fmapM reify

instance (Reify i1 a1, Reify i2 a2) => Reify (i1,i2) (a1,a2) where
    reify (x,y) = (,) <$> reify x <*> reify y

instance (Reify t t', Reify s s', Reify a a') 
         => Reify (Judgement t s a) (Judgement t' s' a') where
    reify (HasType i t) = HasType <$> reify i <*> reify t
    reify (IsType i t)  = IsType <$> reify i <*> reify t
    reify (IsSort i) = IsSort <$> reify i


