{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}

module Scope where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Cont
import Data.Map (Map)
import Data.List
import Text.PrettyPrint

import qualified Data.Map as Map
import qualified Syntax.Abs as C
import Pretty
import Debug

intercalate x = concat . intersperse x

showName = intercalate "."

-- Scope checked terms ----------------------------------------------------

type Var	= String
type Name	= [String]
type ModuleName = Name

data Decl = Section ModuleName Tel [Decl]
	  | Inst ModuleName ModuleName [Expr]
	  | Defn Name Expr Expr
	  | Type Name Expr

type Tel = [(Var, Expr)]

data Expr = Pi Var Expr Expr
	  | Set
	  | App Expr Expr
	  | Lam Var Expr
	  | Var Var
	  | Def Name

section _ [] ds = ds
section m tel ds = [Section m tel ds]

-- Pretty printing --------------------------------------------------------

prettyName :: Name -> Doc
prettyName = hcat . punctuate (text ".") . map text

instance Show Decl where show = show . pretty
instance Show Expr where show = show . pretty

instance Pretty Decl where
    pretty (Section m tel ds) =
	sep [ hsep [ text "section", prettyName m, fsep (map pretty tel), text "where" ]
	    , nest 2 $ vcat $ map pretty ds
	    ]
    pretty (Inst m1 m2 es) =
	sep [ text "module" <+> prettyName m1 <+> text "="
	    , nest 2 $ fsep $ prettyName m2 : map (prettyPrec 10) es
	    ]
    pretty (Defn x t e) =
	sep [ prettyName x
	    , nest 2 $ text ":" <+> pretty t
	    , nest 2 $ text "=" <+> pretty e
	    ]
    pretty (Type x e) =
	sep [ prettyName x <+> text ":"
	    , nest 2 $ pretty e
	    ]

instance Pretty Expr where
    prettyPrec p e = case e of
	Pi "_" a b -> mparens (p > 0) $
	    sep [ prettyPrec 1 a <+> text "->"
		, pretty b
		]
	Pi x a b -> mparens (p > 0) $
	    sep [ parens (text x <+> text ":" <+> pretty a) <+> text "->"
		, pretty b
		]
	Set -> text "Set"
	Lam x t -> mparens (p > 0) $
	    sep [ text "\\" <> text x <+> text "->"
		, pretty t
		]
	App s t -> mparens (p > 1) $
	    sep [ prettyPrec 1 s, prettyPrec 2 t ]
	Var x -> text x
	Def c -> prettyName c

instance Pretty (Var, Expr) where
    pretty (x, e) = parens $ text x <+> text ":" <+> pretty e

-- The scope monad --------------------------------------------------------

type ScopeEnv = Map C.Id Var	-- local vars
type ScopeState = [Scope]	-- stack of modules

data Scope = Scope
	{ scopeName	:: Var
	, scopeContents :: Map C.Id Name
	, scopeModules	:: Map C.Id ModuleName
	}
    deriving Show

type ScopeM = ReaderT ScopeEnv (StateT ScopeState (Either String))

instance Error a => Applicative (Either a) where
    pure = return
    (<*>) = ap

instance (Monad m, Applicative m) => Applicative (StateT s m) where
    pure = return
    (<*>) = ap

instance (Monad m, Applicative m) => Applicative (ReaderT s m) where
    pure = return
    (<*>) = ap

-- Functions on names -----------------------------------------------------

mkVar :: C.Var -> Var
mkVar (C.Var s) = s

mkName :: C.Id -> Name
mkName (C.Id vs) = map mkVar vs

qualify :: Name -> Name -> Name
qualify = (++)

qualifyCId :: Var -> C.Id -> C.Id
qualifyCId x (C.Id vs) = C.Id $ C.Var x : vs

-- Operations -------------------------------------------------------------

data ResolvedName = VarName Var
		  | DefName Name

resolve :: C.Id -> ScopeM ResolvedName
resolve x = do
    vars <- ask
    defs <- get
    maybe (fail $ "undefined name: " ++ show x) return $ mplus
	(VarName <$> Map.lookup x vars)
	(DefName <$> Map.lookup x (Map.unions $ map scopeContents defs))

resolveModule :: C.Id -> ScopeM ModuleName
resolveModule x = Map.lookup x . Map.unions . map scopeModules =<< get

currentModule :: ScopeM Name
currentModule = gets $ reverse . map scopeName

bindVar :: C.Var -> (Var -> ScopeM a) -> ScopeM a
bindVar x ret = local (Map.insert (C.Id [x]) y) (ret y)
    where
	y = mkVar x

bindDef :: C.Var -> ScopeM Name
bindDef x' = do
    m <- currentModule
    let x = C.Id [x']
	y = qualify m $ mkName x
    modify $ \(scope:s) ->
	scope { scopeContents = Map.insert x y $ scopeContents scope } : s
    return y

bindModule :: C.Var -> ScopeM ()
bindModule m = do
    top <- currentModule
    let m' = C.Id [m]
	am = qualify top $ mkName m'
    modify $ \ss -> case ss of
	[]	 -> []
	scope:ss ->
	    scope { scopeModules = Map.insert m' am $ scopeModules scope } : ss

-- | Copy the contents of first argument to a new module specified by the
--   second argument.
copyModule :: ModuleName -> Var -> ScopeM ()
copyModule m x = do
    debug $ "copyModule " ++ showName m ++ " -> " ++ x
    ctx <- gets reverse
    debug $ " topLevel: " ++ showName (map scopeName ctx)
    pushScope x
    debug $ "prefix: " ++ show (commonPrefix ctx m)
    copy $ commonPrefix ctx m
    popScope
    where
	commonPrefix ctx m = takeWhile same $ zip ctx $ tails m
	    where
		same (s, y:_) = scopeName s == y
		same (s, [])  = False

	copy [] = fail $ "panic: empty common prefix " ++ showName m
	copy xs = do
	    top <- currentModule
	    debug $ "top: " ++ showName top
	    debug $ "scope: " ++ show s
	    debug $ "name: " ++ showName m
	    add (isPrefixOf m . init . mkName)
		(onCId $ drop $ length m)
		(qualify top . drop (d + length m)) s
	    where
		(s, _:m) = last xs
		d	 = length xs

	onCId f (C.Id xs) = C.Id $ f xs

	add :: (C.Id -> Bool) -> (C.Id -> C.Id) -> (Name -> Name) -> Scope -> ScopeM ()
	add p key val s = do
	    debug $ "new modules: " ++ show ms
	    debug $ "new definitions: " ++ show ds
	    modify $ \(s:ss) -> s { scopeModules = Map.union ms  $ scopeModules s
				  , scopeContents = Map.union ds $ scopeContents s
				  } : ss
	    where
		move = Map.mapKeys key . Map.map val . Map.filterWithKey (const . p)
		ms = move (scopeModules s)
		ds = move (scopeContents s)

pushScope :: Var -> ScopeM ()
pushScope m = modify $ (:) (Scope m Map.empty Map.empty)

popScope :: ScopeM ()
popScope = do
    top <- currentModule
    modify $ \(s0:s1:ss) ->
	let m0 = C.Id [C.Var $ scopeName s0] in
	s1 { scopeContents = Map.union (scopeContents s1) (defs s0)
	   , scopeModules  = Map.insert m0 (qualify top [scopeName s0])
			   $ Map.union (scopeModules s1)  (mods s0)
	   } : ss
    where
	qual p s = Map.mapKeys (qualifyCId (scopeName s)) (p s)
	defs = qual scopeContents
	mods = qual scopeModules

runScope :: ScopeM a -> Either String a
runScope m = flip evalStateT []
	   $ flip runReaderT Map.empty
	   $ m

-- Scope checking ---------------------------------------------------------

-- | The argument must be a 'C.Module'.
scopeCheckProgram :: C.Decl -> Either String [Decl]
scopeCheckProgram (C.Module m tel ds) = runScope $ do
    pushScope (mkVar m)
    scopeCheckCPS tel $ \tel -> do
	m <- currentModule
	section m tel . concat <$> scopeCheck ds
scopeCheckProgram _ = fail "impossible: top-level program must be a module"

class ScopeCheck c a | c -> a where
    scopeCheck	  :: c -> ScopeM a
    scopeCheckCPS :: c -> (a -> ScopeM b) -> ScopeM b

    scopeCheck	  x	= scopeCheckCPS x return
    scopeCheckCPS x ret = scopeCheck x >>= ret

instance ScopeCheck C.Decl [Decl] where
    scopeCheck d = case d of
	C.Type v e -> do
	    e <- scopeCheck e
	    x <- bindDef v
	    return [ Type x e ]
	C.Def v t e -> do
	    t <- scopeCheck t
	    e <- scopeCheck e
	    x <- bindDef v
	    return [ Defn x t e ] -- non-recursive
	C.Module m tel ds -> do
	    pushScope (mkVar m)
	    top <- currentModule
	    d <- scopeCheckCPS tel $ \tel ->
		section top tel . concat <$> scopeCheck ds
	    popScope
	    bindModule m
	    return d
	C.Inst m1 tel m2 es ->
	    scopeCheckCPS tel $ \tel -> do
		m  <- currentModule
		let m1' = qualify m [mkVar m1]
		m2' <- resolveModule m2
		copyModule m2' (mkVar m1)
		es  <- scopeCheck es
		return $ section ["_"] tel [ Inst m1' m2' es ]

instance ScopeCheck C.Expr Expr where
    scopeCheck e = case e of
	C.Pi x a b -> do
	    a <- scopeCheck a
	    bindVar x $ \x -> Pi x a <$> scopeCheck b
	C.Set -> return Set
	C.App s t -> App <$> scopeCheck s <*> scopeCheck t
	C.Lam x t -> bindVar x $ \x -> Lam x <$> scopeCheck t
	C.Name x  -> do
	    r <- resolve x
	    case r of
		VarName y -> return $ Var y
		DefName c -> return $ Def c

instance ScopeCheck C.Bind (Var, Expr) where
    scopeCheckCPS (C.Bind x e) ret = do
	e <- scopeCheck e
	bindVar x $ \x -> ret (x, e)

instance ScopeCheck c a => ScopeCheck [c] [a] where
    scopeCheck	  = mapM scopeCheck
    scopeCheckCPS = runCont . mapM (Cont . scopeCheckCPS)

