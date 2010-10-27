{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

module Parse where

import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative
import Data.List
import qualified Data.Map as Map

import Syntax
import qualified Lam.Abs as R
import Lam.Par
import Lam.Layout
import Lam.Lex
import Lam.ErrM

parseFile :: FilePath -> IO Sig
parseFile file = parseProg <$> readFile file

parse p s = case p $ myLexer s of
    Bad err -> error err
    Ok p    -> p

parseProg :: String -> Sig
parseProg s = execScope (scopeCheck p) [] Map.empty
    where
	p = parse (pProg . resolveLayout True) s

parseTerm :: Sig -> String -> Exp
parseTerm sig s = evalScope (scopeCheck e) [] sig
    where
	e = parse (pExp . resolveLayout False) s

-- The scope monad

type Context = [Name]
type Scope   = ReaderT [Name] (State Sig)

instance Applicative Scope where
    pure = return
    (<*>) = ap

data Resolved = BoundVar Int | Defined | Unknown

execScope :: Scope a -> Context -> Sig -> Sig
execScope m ctx sig = flip execState sig (runReaderT m ctx)

evalScope :: Scope a -> Context -> Sig -> a
evalScope m ctx sig = flip evalState sig (runReaderT m ctx)

extendContext :: Name -> Scope a -> Scope a
extendContext x = local (x :)

addClause :: Name -> Clause -> Scope ()
addClause x c = modify $ Map.insertWith (flip (++)) x [c]

resolveName :: Name -> Scope Resolved
resolveName x = do
    ctx <- ask
    sig <- get
    let resolved
	    | Just n <- findIndex (x==) ctx = BoundVar n
	    | Map.member x sig		    = Defined
	    | otherwise			    = Unknown
    return resolved

-- Scope checking

class ScopeCheck r i | r -> i where
    scopeCheck :: r -> Scope i
    scopeCheckAnd :: r -> (i -> Scope a) -> Scope a

    scopeCheck x = scopeCheckAnd x return
    scopeCheckAnd x ret = do
	i <- scopeCheck x
	ret i

-- Declarations

instance ScopeCheck R.Prog () where
    scopeCheck (R.Prog ds) = mapM_ scopeCheck ds

instance ScopeCheck R.Decl () where
    scopeCheck (R.Def x ps e) = do
	x  <- scopeCheck $ NewDef x
	scopeCheckAnd ps $ \ps -> do
	e <- scopeCheck e
	addClause x (Clause ps e)

-- Patterns

instance ScopeCheck R.Pat Pat where
    scopeCheckAnd p ret = case p of
	R.WildP			-> extendContext "" $ ret WildP
	R.VarP x		-> scopeCheckAnd (Bound x) $ \_ -> ret VarP
	R.ConP (R.ConName c) ps -> scopeCheckAnd ps $ \ps -> ret $ ConP c ps

-- Expressions

instance ScopeCheck R.Exp Exp where
    scopeCheck e = case e of
	R.Lam xs e -> scopeCheckAnd (map Bound xs) $ \_ -> do
	    v <- scopeCheck e
	    return $ foldr (\_ -> Lam) v xs
	R.App e1 e2 -> App <$> scopeCheck e1 <*> scopeCheck e2
	R.Con (R.ConName c) -> return $ Con c
	R.Var x	-> scopeCheck (SomeName x)

-- Names

newtype NewDef	 = NewDef R.VarName
newtype Bound	 = Bound R.VarName
newtype SomeName = SomeName R.VarName

instance ScopeCheck NewDef Name where
    scopeCheck (NewDef (R.VarName x)) = return x

instance ScopeCheck Bound Name where
    scopeCheckAnd (Bound (R.VarName x)) ret = do
	k <- resolveName x
	case k of
	    BoundVar _ -> fail $ "Shadowing of variable " ++ x
	    _	       -> extendContext x $ ret x

instance ScopeCheck SomeName Exp where
    scopeCheck (SomeName (R.VarName x)) = do
	k <- resolveName x
	case k of
	    BoundVar n	-> return $ Var n
	    Defined	-> return $ Def x
	    Unknown	-> return $ Def x

-- General instances

instance ScopeCheck r i => ScopeCheck [r] [i] where
    scopeCheck = mapM scopeCheck
    scopeCheckAnd [] ret = ret []
    scopeCheckAnd (x : xs) ret =
	scopeCheckAnd x  $ \x ->
	scopeCheckAnd xs $ \xs ->
	ret (x : xs)
