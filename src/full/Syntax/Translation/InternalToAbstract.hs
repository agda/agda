{-# OPTIONS -cpp -fglasgow-exts -fallow-undecidable-instances #-}

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

import Prelude hiding (mapM_, mapM)
import Control.Monad.State hiding (mapM_, mapM)
import Control.Monad.Error hiding (mapM_, mapM)

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List hiding (sort)
import Data.Traversable

import Syntax.Position
import Syntax.Common
import Syntax.Info as Info
import Syntax.Fixity
import Syntax.Abstract as A
import qualified Syntax.Concrete as C
import Syntax.Internal as I
import Syntax.Scope.Base
import Syntax.Scope.Monad

import TypeChecking.Monad as M
import TypeChecking.Reduce
import TypeChecking.Records
import TypeChecking.DisplayForm

import Utils.Monad
import Utils.Tuple
import Utils.Permutation
import Utils.Size

#include "../../undefined.h"

apps :: MonadTCM tcm => (Expr, [Arg Expr]) -> tcm Expr
apps (e, [])		    = return e
apps (e, arg@(Arg Hidden _) : args) =
    do	showImp <- showImplicitArguments
	if showImp then apps (App exprInfo e (unnamed <$> arg), args)
		   else apps (e, args)
apps (e, arg:args)	    =
    apps (App exprInfo e (unnamed <$> arg), args)

exprInfo :: ExprInfo
exprInfo = ExprRange noRange

reifyApp :: MonadTCM tcm => Expr -> [Arg Term] -> tcm Expr
reifyApp e vs = curry apps e =<< reify vs

class Reify i a | i -> a where
    reify :: MonadTCM tcm => i -> tcm a

instance Reify MetaId Expr where
    reify x@(MetaId n) = liftTCM $
	do  mi  <- getMetaInfo <$> lookupMeta x
	    let mi' = Info.MetaInfo (getRange mi)
				    (M.clScope mi)
				    (Just n)
	    iis <- map (snd /\ fst) . Map.assocs
		    <$> gets stInteractionPoints
	    case lookup x iis of
		Just ii@(InteractionId n)
			-> return $ A.QuestionMark $ mi' {metaNumber = Just n}
		Nothing	-> return $ A.Underscore mi'

instance Reify DisplayTerm Expr where
  reify d = case d of
    DTerm v -> reify v
    DWithApp us vs -> do
      us <- reify us
      let wapp [e] = e
	  wapp (e : es) = A.WithApp exprInfo e es
	  wapp [] = __IMPOSSIBLE__
      reifyApp (wapp us) vs

reifyDisplayForm :: MonadTCM tcm => QName -> Args -> tcm A.Expr -> tcm A.Expr
reifyDisplayForm x vs fallback = do
  enabled <- displayFormsEnabled
  if enabled
    then do
      md <- liftTCM $ displayForm x vs
      case md of
        Nothing -> fallback
        Just d  -> reify d
    else fallback

instance Reify Term Expr where
    reify v =
	do  v <- instantiate v
	    case ignoreBlocking v of
		I.Var n vs   ->
		    do  x  <- liftTCM $ nameOfBV n `catchError` \_ -> freshName_ ("@" ++ show n)
			reifyApp (A.Var x) vs
		I.Def x vs   -> reifyDisplayForm x vs $ do
		    n <- getDefFreeVars x
		    reifyApp (A.Def x) $ drop n vs
		I.Con x vs   -> do
		  isR <- isRecord x
		  case isR of
		    True -> do
		      xs <- getRecordFieldNames x
		      vs <- reify $ map unArg vs
		      return $ A.Rec exprInfo $ zip xs vs
		    False -> reifyDisplayForm x vs $ do
                      let hide (Arg _ x) = Arg Hidden x
                      Constructor{conPars = np} <- theDef <$> getConstInfo x
		      scope <- getScope
                      let whocares = A.Underscore (Info.MetaInfo noRange scope Nothing)
                          us = replicate np $ Arg Hidden whocares
                      n  <- getDefFreeVars x
                      es <- reify vs
                      apps (A.Con [x], drop n $ us ++ es)
		I.Lam h b    ->
		    do	(x,e) <- reify b
			return $ A.Lam exprInfo (DomainFree h x) e
		I.Lit l	     -> return $ A.Lit l
		I.Pi a b     ->
		    do	Arg h a <- reify a
			(x,b)   <- reify b
			return $ A.Pi exprInfo [TypedBindings noRange h [TBind noRange [x] a]] b
		I.Fun a b    -> uncurry (A.Fun $ exprInfo)
				<$> reify (a,b)
		I.Sort s     -> reify s
		I.MetaV x vs -> apps =<< reify (x,vs)
		I.BlockedV _ -> __IMPOSSIBLE__

data NamedClause = NamedClause QName I.Clause

instance Reify ClauseBody RHS where
  reify NoBody     = return AbsurdRHS
  reify (Body v)   = RHS <$> reify v
  reify (NoBind b) = reify b
  reify (Bind b)   = reify $ absBody b  -- the variables should already be bound


reifyPatterns :: MonadTCM tcm =>
  I.Telescope -> Permutation -> [Arg I.Pattern] -> tcm [NamedArg A.Pattern]
reifyPatterns tel perm ps =
  evalStateT (reifyArgs ps) 0
  where
    reifyArgs as = map (fmap unnamed) <$> mapM reifyArg as
    reifyArg a   = traverse reifyPat a

    tick = do i <- get; put (i + 1); return i

    translate = (vars !!)
      where
        vars = permute (invertP perm) [0..]

    reifyPat p = case p of
      I.VarP s    -> do
        i <- tick
        let j = translate i
        lift $ A.VarP <$> nameOfBV (size tel - 1 - j)
      I.DotP v    -> tick >> lift (A.DotP i <$> reify v)
      I.LitP l    -> return $ A.LitP l
      I.ConP c ps -> A.ConP i [c] <$> reifyArgs ps
      where
        i = PatRange noRange

instance Reify NamedClause A.Clause where
  reify (NamedClause f (I.Clause tel perm ps body)) = addCtxTel tel $ do
    ps  <- reifyPatterns tel perm ps
    lhs <- return $ LHS info f ps []
    rhs <- reify body
    return $ A.Clause lhs rhs []
    where
      info = LHSRange noRange

instance Reify Type Expr where
    reify (I.El _ t) = reify t

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
			return $ A.App exprInfo (A.Var suc) (Arg NotHidden $ unnamed e)
		I.Lub s1 s2 ->
		    do	lub <- freshName_ "\\/"	-- TODO: hack
			(e1,e2) <- reify (s1,s2)
			let app x y = A.App exprInfo x (Arg NotHidden $ unnamed y)
			return $ A.Var lub `app` e1 `app` e2

instance Reify i a => Reify (Abs i) (Name, a) where
    reify (Abs s v) =
	do  x <- freshName_ s
	    e <- addCtx x (Arg NotHidden $ sort I.Prop) -- type doesn't matter
		 $ reify v
	    return (x,e)

instance Reify I.Telescope A.Telescope where
  reify EmptyTel = return []
  reify (ExtendTel arg tel) = do
    Arg h e <- reify arg
    (x,bs)  <- reify $ betterName tel
    let r = getRange e
    return $ TypedBindings r h [TBind r [x] e] : bs
    where
      betterName (Abs "_" x) = Abs "z" x
      betterName (Abs s   x) = Abs s   x

instance Reify i a => Reify (Arg i) (Arg a) where
    reify = traverse reify

instance Reify i a => Reify [i] [a] where
    reify = traverse reify

instance (Reify i1 a1, Reify i2 a2) => Reify (i1,i2) (a1,a2) where
    reify (x,y) = (,) <$> reify x <*> reify y

instance (Reify t t', Reify a a') 
         => Reify (Judgement t a) (Judgement t' a') where
    reify (HasType i t) = HasType <$> reify i <*> reify t
    reify (IsSort i) = IsSort <$> reify i


