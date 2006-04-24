{-# OPTIONS -fglasgow-exts #-}
{-| Translating from concrete syntax ("AbsCore") to abstract syntax ("Syntax").
-}
module Translation where

import Control.Monad.Reader
import Control.Monad.State
import Data.Set

import qualified AbsCore as C
import Syntax
import Utils

type Subst	= [(C.Ident, Term)]
type Constants	= Set C.Ident

-- | The translation monad. 
type TM = ReaderT Subst (State Constants)

runTM :: Subst -> Constants -> TM a -> a
runTM rho cons m = evalState (runReaderT m rho) cons

bind :: (C.Ident, Term) -> TM a -> TM a
bind b = local (b:)

addConstant :: C.Ident -> TM ()
addConstant x = modify (insert x)

class ToAbstract c a | c -> a where
    toAbstract :: c -> TM a

instance ToAbstract (a -> TM a) (Abs a) where
    toAbstract f =
	do  rho  <- ask
	    cons <- get
	    return $ Abs $ \x -> runTM rho cons (f x)

instance ToAbstract C.Ident Term where
    toAbstract x@(C.Ident s) =
	do  mt <- lookup x <$> ask
	    case mt of
		Nothing	->
		    do	isC <- member x <$> get
			if isC then return $ Con s
			       else fail $ "Unbound variable: " ++ s
		Just t	-> return t

instance ToAbstract C.Term Term where
    toAbstract t =
	case t of
	    C.Lam x t	->
		Lam <$> (toAbstract $ \s -> bind (x,s) $ toAbstract t)
	    C.Var x	-> toAbstract x
	    C.App s t	-> App <$> toAbstract s <*> toAbstract t

