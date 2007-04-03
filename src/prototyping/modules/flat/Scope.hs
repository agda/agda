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
import Debug
import Abstract
import Utils
import Pretty

-- The scope monad --------------------------------------------------------

type ScopeEnv	= Map C.Id Var	-- local vars
data ScopeState = ScopeState
		    { scopeStack :: [Scope]
		    , nextId	 :: Integer
		    }

data Module = Module { moduleName   :: ModuleName
		     , moduleParams :: Int
		     }

data Scope = Scope
	{ scopeName	:: Var
	, scopeContents :: Map C.Id [Name]
	, scopeModules	:: Map C.Id [Module]
	}

instance Show Scope where show = show . pretty

instance Show ScopeState where
  show = unlines . map show . scopeStack

instance Pretty Scope where
  pretty (Scope m ds ms) =
    vcat [ text "scope" <+> text m
	 , nest 2 $ pr ds
	 , nest 2 $ pr $ Map.map (map moduleName) ms
	 ]
    where
      pr m = vcat $ map pr' (Map.toList m)
	where
	  pr' (k, xs) = prId k <+> text "-->" <+> fsep (punctuate comma $ map (text . showName) xs)
      prId (C.Id xs) = hcat $ intersperse (text ".") $ map (text . unVar) xs
      unVar (C.Var x) = x

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
qualifyCId x = onCId (C.Var x :)

onCId f (C.Id xs) = C.Id $ f xs

isSubModuleOf :: Module -> Module -> Bool
isSubModuleOf = flip isPrefixOf `on` moduleName

-- Monad operations -------------------------------------------------------

freshName :: ScopeM Var
freshName = do
  n <- gets nextId
  modify $ \s -> s { nextId = n + 1 }
  return $ "@" ++ show n

modifyStack :: ([Scope] -> [Scope]) -> ScopeM ()
modifyStack f = modify $ \s -> s { scopeStack = f $ scopeStack s }

-- Operations -------------------------------------------------------------

filterKeys :: Ord k => (k -> Bool) -> Map k e -> Map k e
filterKeys p = Map.filterWithKey (const . p)

mapScope :: (Map C.Id [Name] -> Map C.Id [Name]) ->
	    (Map C.Id [Module] -> Map C.Id [Module]) ->
	    Scope -> Scope
mapScope md mm s =
  s { scopeContents = md $ scopeContents s
    , scopeModules  = mm $ scopeModules  s
    }

filterScope :: (C.Id -> Bool) -> (C.Id -> Bool) -> Scope -> Scope
filterScope pd pm = mapScope (filterKeys pd) (filterKeys pm)

unionScope :: Scope -> Scope -> Scope
unionScope s1 s2 = mapScope (+++ scopeContents s2) (+++ scopeModules s2) s1
  where (+++) = Map.unionWith (++)

unionsScope :: [Scope] -> Scope
unionsScope = foldr1 unionScope

data ResolvedName = VarName Var
		  | DefName Name

resolve :: C.Id -> ScopeM ResolvedName
resolve x = do
    vars <- ask
    defs <- gets $ scopeContents . unionsScope . scopeStack
    case Map.lookup x vars of
      Just v  -> return $ VarName v
      Nothing -> case Map.lookup x defs of
	Nothing	 -> do
	  debug . show =<< get
	  fail $ "not in scope: " ++ show x
	Just [c] -> return $ DefName c
	Just cs	 -> do
	  debug . show =<< get
	  fail $ "ambiguous name: " ++ show x ++ " can refer to " ++ intercalate ", " (map showName cs)

resolveModule :: C.Id -> ScopeM Module
resolveModule x = do
  ms <- gets $ scopeModules . unionsScope . scopeStack
  case Map.lookup x ms of
    Nothing -> do
      s <- get
      debug $ show s
      fail $ "module not in scope: " ++ show x
    Just [m] -> return m
    Just ms  -> do
      debug . show =<< get
      fail $ "ambiguous module: " ++ show x ++ " can refer to " ++ intercalate ", " (map (showName . moduleName) ms)

currentModule :: ScopeM Module
currentModule = do
  name <- gets $ reverse . map scopeName . scopeStack
  n    <- asks Map.size
  return $ Module name n

showState :: String -> ScopeM ()
showState msg = do
  s <- get
  debug $ msg ++ "\n " ++ show s

bindVar :: C.Var -> (Var -> ScopeM a) -> ScopeM a
bindVar x ret = local (Map.insert (C.Id [x]) y) (ret y)
    where
	y = mkVar x

bindDef :: C.Var -> ScopeM Name
bindDef x' = do
    m <- moduleName <$> currentModule
    let x = C.Id [x']
	y = qualify m $ mkName x
    debug $ "in module " ++ showName m ++ " binding " ++ show x' ++ " --> " ++ showName y
    modifyStack $ \(scope:s) ->
	scope { scopeContents = Map.insertWith (++) x [y] $ scopeContents scope } : s
    return y

bindModule :: C.Var -> ScopeM ()
bindModule m = do
    top <- moduleName <$> currentModule
    fv  <- asks Map.size
    let m' = C.Id [m]
	am = qualify top $ mkName m'
    debug $ "in module " ++ showName top ++ " binding module " ++ show m ++ " --> " ++ showName am
    modifyStack $ \ss -> case ss of
	[]	 -> []
	scope:ss -> mapScope id (Map.insertWith (++) m' [Module am fv]) scope : ss

matchPrefix :: C.Id -> ScopeM Scope
matchPrefix m = do
  s <- gets $ unionsScope . scopeStack
  return $ filterScope (isPrefix m) (isPrefix m) s
  where isPrefix (C.Id xs) (C.Id ys) = isPrefixOf xs ys && xs /= ys

-- All concrete names are assumed to have the same prefix (specified by the
-- first argument)
dropPrefix :: C.Id -> Scope -> Scope
dropPrefix (C.Id xs) = mapScope dropPrefix dropPrefix
  where
    dropPrefix = Map.mapKeys (\(C.Id ys) -> C.Id (drop (length xs) ys))

-- Apply scope modifiers to a scope
applyModifiers :: [C.Modifier] -> Scope -> Scope
applyModifiers xs s = foldr apply s xs
  where
    apply :: C.Modifier -> Scope -> Scope
    apply (C.Using xs) s = filterScope' (`elem` ds) (`elem` ms) s
      where
	ms = [ C.Id [x] | C.ImportMod x <- xs ]
	ds = [ C.Id [x] | C.ImportDef x <- xs ]
    apply (C.Hiding xs) s = filterScope' (`notElem` ds) (`notElem` ms) s
      where
	ms = [ C.Id [x] | C.ImportMod x <- xs ]
	ds = [ C.Id [x] | C.ImportDef x <- xs ]
    apply (C.Renaming rs) s = mapScope (rename ds ms) (rename ms ms) s
      where
	ms = [ (C.Id [x], C.Id [y]) | C.To (C.ImportMod x) y <- rs ]
	ds = [ (C.Id [x], C.Id [y]) | C.To (C.ImportDef x) y <- rs ]

	rename ds ms = Map.mapKeys ren
	  where
	    ren (C.Id [])	= error $ "panic: empty name"
	    ren k@(C.Id [_])    = maybe k id $ lookup k ds
	    ren k@(C.Id (m:xs)) = C.Id (m'' ++ xs)
	      where
		m'	 = C.Id [m]
		C.Id m'' = maybe m' id $ lookup m' ms

    filterDef pd pm x
      | len == 1  = pd x
      | len > 1	  = filterMod pm x
      | otherwise = error "panic: empty name"
      where
	len = length (mkName x)
    filterMod pm      = pm . onCId (take 1)

    filterScope' pd pm = filterScope (filterDef pd pm) (filterMod pm)

-- Merge the given scope with the current scope
addScope :: Scope -> ScopeM ()
addScope s' = modifyStack $ \(s:ss) -> unionScope s s' : ss

-- | In the top scope, make all canonical refer to that scope.
freshCanonicalNames :: ModuleName -> ModuleName -> ScopeM ()
freshCanonicalNames old new =
  modifyStack $ \(s : ss) -> mapScope (rename id) (rename onName) s : ss
  where
    onName f m = m { moduleName = f $ moduleName m }

    rename f = Map.mapWithKey (ren f)
    -- Change a binding M.x -> N.M'.y to M.x -> m.M'.y
    -- where M and M' have the same length.
    ren f (C.Id xs) ys = map (f qdq) ys
      where
	qdq y
	  | old `isPrefixOf` y = qualify new . dequalify $ y
	  | otherwise	       = y

	dequalify = drop (length old)

pushScope :: Var -> ScopeM ()
pushScope m = modifyStack $ (:) (Scope m Map.empty Map.empty)

popScope :: ScopeM ()
popScope = do
    top <- currentModule
    modifyStack $ \(s0:s1:ss) -> unionScope s1 (mapScope (qual s0) (qual s0) s0) : ss
    where
	qual s m = Map.mapKeys (qualifyCId (scopeName s)) m

runScope :: ScopeM a -> Either String a
runScope m = flip evalStateT (ScopeState [] 0)
	   $ flip runReaderT Map.empty
	   $ m

-- Scope checking ---------------------------------------------------------

-- | The argument must be a 'C.Module'.
scopeCheckProgram :: C.Decl -> Either String [Decl]
scopeCheckProgram (C.Module m tel ds) = runScope $ do
    pushScope (mkVar m)
    scopeCheckCPS tel $ \tel -> do
	m <- moduleName <$> currentModule
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
	    top <- moduleName <$> currentModule
	    d <- scopeCheckCPS tel $ \tel ->
		section top tel . concat <$> scopeCheck ds
	    popScope
	    bindModule m
	    return d
	C.Inst m1 tel m2 es mods ->
	    scopeCheckCPS tel $ \tel -> do
		showState "instantiating"
		m  <- moduleName <$> currentModule
		let m1' = qualify m [mkVar m1]
		m2' <- resolveModule m2
		es  <- scopeCheck es
		pushScope (mkVar m1)
		addScope . applyModifiers mods . dropPrefix m2 =<< matchPrefix m2
		showState "pushed and opened"
		debug $ "m1' = " ++ show m1'
		debug $ "m2' = " ++ show (moduleName m2')
		freshCanonicalNames (moduleName m2') m1'
		popScope
		bindModule m1
		showState "finished"
		return $ section ["_"] tel [ Inst m1' (moduleName m2') es ]
	C.Open m mods -> do
	  current <- currentModule
	  m'	  <- resolveModule m
	  debug $ "opening module " ++ show (moduleName m')
	  debug $ "     in module " ++ show (moduleName current)

	  -- Opening a submodule or opening into a non-parameterised module
	  -- is fine. Otherwise we have to create a temporary module.
	  if m' `isSubModuleOf` current || moduleParams current == 0
	    then do 
	      addScope . applyModifiers mods . dropPrefix m =<< matchPrefix m
	      return []
	    else do
	      tmp <- C.Var <$> freshName
	      concat <$> scopeCheck
		[ C.Inst tmp [] m [] mods
		, C.Open (C.Id [tmp]) []
		]

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

