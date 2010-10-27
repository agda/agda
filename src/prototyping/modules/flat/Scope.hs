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
	, scopePublic	:: NameSpace
	, scopePrivate	:: NameSpace
	}

data NameSpace = NameSpace
	{ nsContents :: Map C.Id [Name]
	, nsModules  :: Map C.Id [Module]
	}

instance Show Scope where show = show . pretty

instance Show ScopeState where
  show = unlines . map show . scopeStack

instance Pretty Scope where
  pretty (Scope m pub pri) =
    vcat [ text "scope" <+> text m
	 , nest 2 $ text "public:"
	 , nest 4 $ pretty pub
	 , nest 2 $ text "private:"
	 , nest 4 $ pretty pri
	 ]

instance Pretty NameSpace where
  pretty (NameSpace ds ms) =
    vcat [ pr ds
	 , pr $ Map.map (map moduleName) ms
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
mapScope md mm s = s { scopePublic  = mapNS $ scopePublic s
		     , scopePrivate = mapNS $ scopePrivate s
		     }
  where
    mapNS ns =
      ns { nsContents = md $ nsContents ns
	 , nsModules  = mm $ nsModules  ns
	 }

zipScope :: (Map C.Id [Name] -> Map C.Id [Name] -> Map C.Id [Name]) ->
	    (Map C.Id [Module] -> Map C.Id [Module] -> Map C.Id [Module]) ->
	    Scope -> Scope -> Scope
zipScope fd fm s1 s2 =
  s1 { scopePublic  = (zipNS `on` scopePublic ) s1 s2
     , scopePrivate = (zipNS `on` scopePrivate) s1 s2
     }
  where
    zipNS = zipNameSpace fd fm

zipNameSpace fd fm ns1 ns2 =
    ns1 { nsContents = (fd `on` nsContents) ns1 ns2
	, nsModules  = (fm `on` nsModules ) ns1 ns2
	}

filterScope :: (C.Id -> Bool) -> (C.Id -> Bool) -> Scope -> Scope
filterScope pd pm = mapScope (filterKeys pd) (filterKeys pm)

scopeContents :: Scope -> Map C.Id [Name]
scopeContents s = (Map.unionWith (++) `on` nsContents) (scopePublic s) (scopePrivate s)

scopeModules :: Scope -> Map C.Id [Module]
scopeModules s = (Map.unionWith (++) `on` nsModules) (scopePublic s) (scopePrivate s)

unionScope :: Scope -> Scope -> Scope
unionScope = zipScope (+++) (+++)
  where (+++) = Map.unionWith (++)

unionsScope :: [Scope] -> Scope
unionsScope = foldr1 unionScope

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
    apply (C.Using xs)	  = filterNames elem	elem	xs
    apply (C.Hiding xs)	  = filterNames notElem notElem xs
    apply (C.Renaming rs) = mapScope (rename ds ms) (rename ms ms)
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

    filterNames pd pm xs = filterScope' (flip pd ds) (flip pm ms)
      where
	ms = [ C.Id [x] | C.ImportMod x <- xs ]
	ds = [ C.Id [x] | C.ImportDef x <- xs ]

    filterDef pd pm x
      | len == 1  = pd x
      | len > 1	  = filterMod pm x
      | otherwise = error "panic: empty name"
      where
	len = length (mkName x)
    filterMod pm      = pm . onCId (take 1)

    filterScope' pd pm = filterScope (filterDef pd pm) (filterMod pm)

changeAccess :: C.Access -> Scope -> Scope
changeAccess acc s =
    s { scopePrivate = pr
      , scopePublic  = pu
      }
  where
    unionNS = zipNameSpace (+++) (+++)
    (+++)   = Map.unionWith (++)
    emp	    = emptyNameSpace
    full    = unionNS (scopePublic s) (scopePrivate s)
    (pu, pr) = case acc of
      C.Public	-> (full, emp)
      C.Private -> (emp, full)

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
	scope { scopePublic = (scopePublic scope)
		  { nsContents = Map.insertWith (++) x [y] $ nsContents $ scopePublic scope
		  }
	      } : s
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
	scope:ss ->
	  scope { scopePublic = (scopePublic scope)
		  { nsModules = Map.insertWith (++) m' [Module am fv] $ nsModules $ scopePublic scope
		  }
		} : ss

matchPrefix :: C.Id -> ScopeM Scope
matchPrefix m = do
  s <- gets $ unionsScope . scopeStack
  return $ filterScope (isPrefix m) (isPrefix m) s
  where isPrefix (C.Id xs) (C.Id ys) = isPrefixOf xs ys && xs /= ys

-- Merge the given scope with the current scope
addScope :: Scope -> ScopeM ()
addScope s' = modifyStack $ \(s:ss) -> unionScope s s' : ss

-- | In the top scope, make all canonical refer to that scope.
freshCanonicalNames :: ModuleName -> ModuleName -> ScopeM ()
freshCanonicalNames old new =
  modifyStack $ \(s : ss) -> mapScope (rename id) (rename onName) s : ss
  where
    onName f m = m { moduleName = f $ moduleName m }

    rename f = Map.map (ren f)
    -- Change a binding M.x -> N.M'.y to M.x -> m.M'.y
    -- where M and M' have the same length.
    ren f ys = map (f qdq) ys
      where
	qdq y
	  | old `isPrefixOf` y = qualify new . dequalify $ y
	  | otherwise	       = y

	dequalify = drop (length old)

-- | Open a module. Assumes that all checks have been made to see that it's ok to
--   open it.
openModule_ :: C.Id -> C.Access -> [C.Modifier] -> ScopeM ()
openModule_ m access mods =
  addScope . changeAccess access
           . applyModifiers mods
           . dropPrefix m =<< matchPrefix m

pushScope :: Var -> ScopeM ()
pushScope m = modifyStack $ (:) (Scope m emptyNameSpace emptyNameSpace)

emptyNameSpace :: NameSpace
emptyNameSpace = NameSpace Map.empty Map.empty

popScope :: ScopeM ()
popScope = do
    top <- currentModule
    modifyStack $ \(s0:s1:ss) ->
      unionScope s1 (mapScope (qual s0) (qual s0) $ noPrivate s0) : ss
    where
	qual s m = Map.mapKeys (qualifyCId (scopeName s)) m
	noPrivate s = s { scopePrivate = emptyNameSpace }

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
	C.Def v tel t C.NoRHS ->
	  scopeCheckCPS tel $ \tel -> do
	    t <- scopeCheck t
	    x <- bindDef v
	    return [ Type x $ foldr (uncurry Pi) t tel ]
	C.Def v tel t (C.RHS e whr) ->
	  scopeCheckCPS tel $ \tel -> do
	    t <- scopeCheck t
	    ds <- case whr of
	      C.NoWhere -> return []
	      _		-> do
		(m, tel, ds) <- case whr of
		  C.AnyWhere ds -> do
		    m <- C.Var <$> freshName
		    return (m, [], ds)
		  C.SomeWhere m tel ds -> return (m, tel, ds)
		  C.NoWhere	       -> error "impossible"
		concat <$> scopeCheck [ C.Module m tel ds
				      , C.Open (C.Id [m]) C.Private []
				      ]
	    e <- scopeCheck e
	    x <- bindDef v  -- non-recursive
	    return [ Defn x tel t e ds ]
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
		openModule_ m2 C.Public mods
		showState "pushed and opened"
		debug $ "m1' = " ++ show m1'
		debug $ "m2' = " ++ show (moduleName m2')
		freshCanonicalNames (moduleName m2') m1'
		popScope
		bindModule m1
		showState "finished"
		return $ section ["_"] tel [ Inst m1' (moduleName m2') es ]
	C.Open m access mods -> do
	  current <- currentModule
	  m'	  <- resolveModule m
	  debug $ "opening module " ++ show (moduleName m')
	  debug $ "     in module " ++ show (moduleName current)

	  -- Opening a submodule or opening into a non-parameterised module
	  -- is fine. Otherwise we have to create a temporary module.
	  if m' `isSubModuleOf` current || moduleParams current == 0
	    then do
	      openModule_ m access mods
	      return []
	    else do
	      tmp <- C.Var <$> freshName
	      concat <$> scopeCheck
		[ C.Inst tmp [] m [] mods
		, C.Open (C.Id [tmp]) access []
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
