{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, PatternGuards #-}
module Scope.Check where

import Control.Arrow ((***), (&&&))
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error
import Data.Monoid
import qualified Data.Map as Map
import Data.Map (Map)

import qualified Syntax.Abs as C
import Syntax.Abstract
import Syntax.Abstract.Pretty
import Syntax.Print

data ScopeError = ScopeError SrcLoc String

instance Show ScopeError where
  show (ScopeError pos err) = show pos ++ ": " ++ err

instance Error ScopeError where
  strMsg = ScopeError noSrcLoc

data Scope = Scope
  { inScope :: Map String NameInfo
  }

initScope :: Scope
initScope = Scope $ Map.fromList
  [ ("refl", DefName (Name noSrcLoc "refl")  2)
  , ("J",    DefName (Name noSrcLoc "J")     3)
  , ("K",    DefName (Name noSrcLoc "K")     2) ]

type Hiding = Int

data NameInfo = VarName Name | DefName Name Hiding | ConName Name Hiding | ProjName Name Hiding

infoName :: NameInfo -> Name
infoName (VarName x)    = x
infoName (DefName x _)  = x
infoName (ConName x _)  = x
infoName (ProjName x _) = x

infoStringName :: NameInfo -> String
infoStringName i = s
  where Name _ s = infoName i

infoHiding :: NameInfo -> Hiding
infoHiding (VarName _)    = 0
infoHiding (DefName _ n)  = n
infoHiding (ConName _ n)  = n
infoHiding (ProjName _ n) = n

instance HasSrcLoc NameInfo where
  srcLoc i = case i of
    VarName x    -> srcLoc x
    DefName x _  -> srcLoc x
    ConName x _  -> srcLoc x
    ProjName x _ -> srcLoc x

newtype Check a = Check { unCheck :: ReaderT Scope (Either ScopeError) a }
  deriving (Functor, Applicative, Monad, MonadReader Scope, MonadError ScopeError)

type CCheck a = forall b. (a -> Check b) -> Check b
type CCheck_  = forall b. Check b -> Check b

mapC :: (a -> CCheck b) -> [a] -> CCheck [b]
mapC f [] ret = ret []
mapC f (x : xs) ret = f x $ \y -> mapC f xs $ \ys -> ret (y : ys)

concatMapC :: (a -> CCheck [b]) -> [a] -> CCheck [b]
concatMapC f xs ret = mapC f xs $ ret . concat

scopeError :: HasSrcLoc i => i -> String -> Check a
scopeError p err = throwError $ ScopeError (srcLoc p) err

reservedNames = ["_", "Set"]

impossible err = fail $ "impossible: " ++ err

mkName :: Int -> Int -> String -> Name
mkName l c s = Name (SrcLoc l c) s

mkVarInfo :: C.Name -> NameInfo
mkVarInfo (C.Name ((l, c), s)) = VarName (mkName l c s)

mkDefInfo :: C.Name -> Hiding -> NameInfo
mkDefInfo (C.Name ((l, c), s)) = DefName (mkName l c s)

mkConInfo :: C.Name -> Hiding -> NameInfo
mkConInfo (C.Name ((l, c), s)) = ConName (mkName l c s)

mkProjInfo :: C.Name -> Hiding -> NameInfo
mkProjInfo (C.Name ((l, c), s)) = ProjName (mkName l c s)

resolveName'' :: C.Name -> Check (Maybe NameInfo)
resolveName'' (C.Name ((l, c), s))
  | elem s reservedNames = impossible "reserved names should not end up in resolveName"
  | otherwise = asks $ Map.lookup s . inScope

resolveName' :: C.Name -> Check NameInfo
resolveName' x = do
  mi <- resolveName'' x
  case mi of
    Nothing -> scopeError x $ "Not in scope: " ++ printTree x
    Just i  -> return i

resolveName :: C.Name -> Check (Head, Hiding)
resolveName x@(C.Name ((l, c), s)) = do
  i <- resolveName' x
  case i of
    VarName _   -> return (Var y, 0)
    DefName _ n -> return (Def y, n)
    ConName _ n -> return (Con y, n)
    ProjName{}  -> scopeError x $ "Did not expect projection here: " ++ printTree x
  where
    y = Name (SrcLoc l c) s

checkShadowing :: NameInfo -> Maybe NameInfo -> Check ()
checkShadowing _ Nothing   = return ()
checkShadowing VarName{} _ = return ()
checkShadowing i (Just j)  =
  scopeError i $ "Cannot shadow previous definition of " ++ infoStringName j ++
                 " at " ++ show (srcLoc j)

bindName :: NameInfo -> CCheck Name
bindName i ret = do
  checkShadowing i =<< asks (Map.lookup s . inScope)
  flip local (ret x) $ \e -> e { inScope = Map.insert s i $ inScope e }
  where
    s = infoStringName i
    x = infoName i

checkHiding :: C.Expr -> Check (Hiding, C.Expr)
checkHiding e = case e of
  C.Fun a b  -> (id *** C.Fun a) <$> checkHiding b
  C.Pi (C.Tel tel) b -> do
    (n, tel, stop) <- telHiding tel
    if stop then return (n, C.Pi (C.Tel tel) b)
            else do
      (m, b) <- checkHiding b
      return (n + m, C.Pi (C.Tel tel) b)
  _ -> return (0, e)
  where
    telHiding [] = return (0, [], False)
    telHiding bs@(C.Bind{} : _) = return (0, bs, True)
    telHiding (C.HBind xs e : bs) = do
      (n, bs, stop) <- telHiding bs
      return (n + length xs, C.Bind xs e : bs, stop)

scopeCheck :: C.Program -> Either ScopeError [Decl]
scopeCheck (C.Prog ds) = flip runReaderT initScope $ unCheck $ concatMapC checkDecl ds return

isSet :: C.Name -> Check ()
isSet (C.Name ((l, c), "Set")) = return ()
isSet e = scopeError e "The type of a datatype or record should be Set"

isDefHead :: Head -> String -> Check Name
isDefHead (Def x) _ = return x
isDefHead h err     = scopeError h err

isConHead :: Head -> String -> Check Name
isConHead (Con x) _ = return x
isConHead h err     = scopeError h err

resolveDef :: C.Name -> Check (Name, Hiding)
resolveDef x = do
  (h, n) <- resolveName x
  x      <- isDefHead h $ printTree x ++ " should be a defined name"
  return (x, n)

resolveCon :: C.Name -> Check (Name, Hiding)
resolveCon x = do
  (h, n) <- resolveName x
  x      <- isConHead h $ printTree x ++ " should be a constructor"
  return (x, n)

checkHiddenNames :: Hiding -> [C.HiddenName] -> Check [C.Name]
checkHiddenNames 0 (C.NotHidden x : xs) = (x :) <$> checkHiddenNames 0 xs
checkHiddenNames n (C.NotHidden x : _)  = scopeError x $ "Expected implicit binding of " ++ printTree x
checkHiddenNames 0 (C.Hidden x : _)     = scopeError x $ "Expected explicit binding of " ++ printTree x
checkHiddenNames n (C.Hidden x : xs)    = (x :) <$> checkHiddenNames (n - 1) xs
checkHiddenNames 0 []                   = return []
checkHiddenNames _ []                   = impossible "checkHiddenNames _ []"

isParamDecl :: C.Params -> Maybe [C.Binding]
isParamDecl C.NoParams       = Just []
isParamDecl (C.ParamDecl ps) = Just ps
isParamDecl C.ParamDef{}     = Nothing

isParamDef :: C.Params -> Maybe [C.HiddenName]
isParamDef C.NoParams      = Just []
isParamDef C.ParamDecl{}   = Nothing
isParamDef (C.ParamDef xs) = Just xs

checkDecl :: C.Decl -> CCheck [Decl]
checkDecl d ret = case d of
  C.TypeSig x e -> do
    (n, a) <- checkScheme e
    bindName (mkDefInfo x n) $ \x -> ret [TypeSig $ Sig x a]
  C.Data x pars (C.NoDataBody set) | Just ps <- isParamDecl pars ->
    dataOrRecDecl x ps set
  C.Record x pars (C.NoRecordBody set) | Just ps <- isParamDecl pars ->
    dataOrRecDecl x ps set
  C.Data x pars (C.DataBody cs) | Just xs <- isParamDef pars -> do
    (x, n) <- resolveDef x
    when (n > length xs) $ scopeError x $ "Too few parameters to " ++ show x ++
                                          " (implicit arguments must be explicitly bound here)"
    xs <- checkHiddenNames n xs
    let is = map mkVarInfo xs
    xs <- mapC bindName is $ return
    mapC (checkConstructor is) cs $ \cs ->
      ret [DataDef x xs cs]
  C.Record x pars (C.RecordBody con fs) | Just xs <- isParamDef pars -> do
    (x, n) <- resolveDef x
    when (n > length xs) $ scopeError x $ "Too few parameters to " ++ show x ++
                                          " (implicit arguments must be explicitly bound here)"
    xs <- checkHiddenNames n xs
    let is = map mkVarInfo xs
    xs <- mapC bindName is $ return
    mapC (checkField is) fs $ \fs ->
      bindName (mkConInfo con 0) $ \con ->
        ret [RecDef x xs con fs]
  C.Data{}   -> scopeError d $ "Bad data declaration"
  C.Record{} -> scopeError d $ "Bad record declaration"
  C.FunDef f ps b -> do
    (f, n) <- resolveDef f
    ps     <- insertImplicitPatterns (srcLoc f) n ps
    (ps, b) <- mapC checkPattern ps $ \ps -> (,) ps <$> checkExpr b
    ret [FunDef f ps b]
  C.Open x -> do
    h <- fst <$> resolveName x
    isDefHead h $ "Open module should be the name of a defined record: " ++ printTree x
    ret []
  where
    dataOrRecDecl x ps set = do
      isSet set
      (n, a) <- checkScheme (C.Pi (C.Tel ps) (C.App [C.Arg $ C.Id set]))
      bindName (mkDefInfo x n) $ \x -> ret [TypeSig $ Sig x a]

checkConstructor :: [NameInfo] -> C.Constr -> CCheck TypeSig
checkConstructor xs (C.Constr c e) ret =
  mapC bindName xs $ \_ -> do
    (n, a) <- checkScheme e
    bindName (mkConInfo c n) $ \c -> ret (Sig c a)

checkField :: [NameInfo] -> C.Constr -> CCheck TypeSig
checkField xs (C.Constr c e) ret =
  mapC bindName xs $ \_ -> do
    (n, a) <- checkScheme e
    bindName (mkProjInfo c n) $ \c -> ret (Sig c a)

checkScheme :: C.Expr -> Check (Hiding, Expr)
checkScheme e = do
  (n, e) <- checkHiding e
  a      <- checkExpr e
  return (n, a)

cMeta :: HasSrcLoc a => a -> C.Expr
cMeta x = C.App [C.Arg $ C.Id $ C.Name ((l, c), "_")]
  where SrcLoc l c = srcLoc x

cWild :: HasSrcLoc a => a -> C.Pattern
cWild x = C.IdP (C.Name ((l, c), "_"))
  where SrcLoc l c = srcLoc x

insertImplicit :: SrcLoc -> Hiding -> [C.Arg] -> Check [C.Expr]
insertImplicit p 0 (C.Arg e : args)  = (e :) <$> insertImplicit (srcLoc e) 0 args
insertImplicit p 0 (C.HArg e : _)    = scopeError e $ "Unexpected implicit application " ++ printTree e
insertImplicit p 0 []                = return []
insertImplicit p n (C.HArg e : args) = (e :) <$> insertImplicit (srcLoc e) (n - 1) args
insertImplicit p n args              = (cMeta p :) <$> insertImplicit p (n - 1) args

insertImplicitPatterns :: SrcLoc -> Hiding -> [C.Pattern] -> Check [C.Pattern]
insertImplicitPatterns p 0 (C.HideP e : _)  = scopeError e $ "Unexpected implicit pattern " ++ printTree e
insertImplicitPatterns p 0 (e : args)       = (e :) <$> insertImplicitPatterns (srcLoc e) 0 args
insertImplicitPatterns p 0 []               = return []
insertImplicitPatterns p n (C.HideP e : ps) = (e :) <$> insertImplicitPatterns (srcLoc e) (n - 1) ps
insertImplicitPatterns p n ps               = (cWild p :) <$> insertImplicitPatterns p (n - 1) ps

type PAppView = (C.Name,  [C.Pattern])

pAppView :: C.Pattern -> Check PAppView
pAppView p = case p of
  C.AppP p q -> applyTo q <$> pAppView p
  C.IdP x    -> return (x, [])
  C.HideP p  -> scopeError p $ "Unexpected implicit pattern: " ++ printTree p
  where
    applyTo q (c, ps) = (c, ps ++ [q])

checkPattern :: C.Pattern -> CCheck Pattern
checkPattern p ret = do
  (c, ps) <- pAppView p
  case (c, ps) of
    (C.Name ((l, c), "_"), []) -> ret $ WildP (SrcLoc l c)
    (x, []) -> do
      mi <- resolveName'' x
      case mi of
        Just ConName{} -> checkCon x [] ret
        _              -> bindName (mkVarInfo x) $ ret . VarP
    (c, ps) -> checkCon c ps ret
  where
    checkCon c ps ret = do
      (c, n) <- resolveCon c
      ps <- insertImplicitPatterns (srcLoc c) n ps
      mapC checkPattern ps $ \ps -> ret (ConP c ps)

checkExpr :: C.Expr -> Check Expr
checkExpr e = case e of
  C.Pi (C.Tel tel) b ->
    checkTel tel $ \tel -> do
      b <- checkExpr b
      return $ foldr (uncurry Pi) b tel
  C.Fun a b -> Fun <$> checkExpr a <*> checkExpr b
  C.Lam xs e ->
    mapC (bindName . mkVarInfo) xs $ \xs ->
    flip (foldr Lam) xs <$> checkExpr e
  C.Eq x y -> do
    x <- checkExpr x
    y <- checkExpr y
    return $ Equal (Meta $ srcLoc x) x y
  C.Id{}  -> checkApp e
  C.App{} -> checkApp e
  where
    checkApp e = do
      app <- appView e
      case app of
        NotApp e  -> checkExpr e
        CApp x es -> do
          (z, n) <- checkAppHead x
          case z of
            IsProj x -> case es of
              []   -> scopeError e $ "Record projections must be applied: " ++ printTree e
              C.HArg _ : _ -> scopeError e $ "Unexpected implicit argument to projection function: " ++ printTree e
              C.Arg e : es -> do
                e <- checkExpr e
                doProj x e =<< checkArgs e n es
            NotProj h  -> App h <$> checkArgs z n es
            HeadSet p  -> return $ Set p
            HeadMeta p -> return $ Meta p
    doProj x (App h es1) es2 = return $ App h (es1 ++ [Proj x] ++ es2)
    doProj x e _ = scopeError x $ "Cannot project " ++ show x ++ " from " ++ show e

checkArgs :: HasSrcLoc a => a -> Hiding -> [C.Arg] -> Check [Elim]
checkArgs x n es = map Apply <$> (mapM checkExpr =<< insertImplicit (srcLoc x) n es)

data AppHead = IsProj Name | NotProj Head | HeadSet SrcLoc | HeadMeta SrcLoc

instance HasSrcLoc AppHead where
  srcLoc h = case h of
    IsProj x   -> srcLoc x
    NotProj h  -> srcLoc h
    HeadSet p  -> p
    HeadMeta p -> p

data AppView = CApp C.Name [C.Arg]
             | NotApp C.Expr

appView :: C.Expr -> Check AppView
appView e = case e of
  C.App (arg@C.HArg{} : _) ->
    scopeError arg $ "Unexpected curly braces: " ++ printTree arg
  C.App (C.Arg e : es) -> applyTo es =<< appView e
  C.App []             -> impossible "appView: empty application"
  C.Id x               -> return $ CApp x []
  C.Lam{}              -> notApp
  C.Pi{}               -> notApp
  C.Fun{}              -> notApp
  C.Eq{}               -> notApp
  where
    notApp = return $ NotApp e
    applyTo []  app          = return app
    applyTo es2 (CApp x es1) = return $ CApp x $ es1 ++ es2
    applyTo es  (NotApp e)   = scopeError e $ printTree e ++ " cannot be applied to arguments"

checkAppHead :: C.Name -> Check (AppHead, Hiding)
checkAppHead (C.Name ((l, c), "_"))   = return (HeadMeta $ SrcLoc l c, 0)
checkAppHead (C.Name ((l, c), "Set")) = return (HeadSet $ SrcLoc l c, 0)
checkAppHead x = do
  i <- resolveName' x
  case i of
    ProjName x n -> return (IsProj x, n)
    VarName x    -> return (NotProj $ Var x, 0)
    ConName x n  -> return (NotProj $ Con x, n)
    DefName x n  -> return (NotProj $ Def x, n)

checkTel :: [C.Binding] -> CCheck [(Name, Expr)]
checkTel = concatMapC checkBinding

checkBinding :: C.Binding -> CCheck [(Name, Expr)]
checkBinding b@C.HBind{} _ = scopeError b $ "Implicit binding must be on top level: " ++ printTree b
checkBinding (C.Bind args e) ret = do
  xs <- mapM argName args
  let is = map mkVarInfo xs
  a <- checkExpr e
  mapC bindName is $ \ys -> ret [ (y, a) | y <- ys ]

argName :: C.Arg -> Check C.Name
argName (C.Arg (C.Id x)) = return x
argName a = scopeError a $ "Expected variable name: " ++ printTree a

-- SrcLoc instances --

instance HasSrcLoc C.Name where
  srcLoc (C.Name ((l, c), _)) = SrcLoc l c

instance HasSrcLoc C.Expr where
  srcLoc e = case e of
    C.Lam (x:_) _ -> srcLoc x
    C.Lam [] _    -> error $ "nullary lambda: " ++ show e
    C.Pi tel _    -> srcLoc tel
    C.Fun a _     -> srcLoc a
    C.Eq x _      -> srcLoc x
    C.App (e:_)   -> srcLoc e
    C.App []      -> error "empty application"
    C.Id x        -> srcLoc x

instance HasSrcLoc C.Arg where
  srcLoc (C.Arg e)  = srcLoc e
  srcLoc (C.HArg e) = srcLoc e

instance HasSrcLoc C.Telescope where
  srcLoc (C.Tel (b : _)) = srcLoc b
  srcLoc tel = error $ "empty telescope: " ++ show tel

instance HasSrcLoc C.Binding where
  srcLoc (C.Bind  (x:_) _) = srcLoc x
  srcLoc (C.HBind (x:_) _) = srcLoc x
  srcLoc b = error $ "binding no names: " ++ show b

instance HasSrcLoc C.Decl where
  srcLoc d = case d of
    C.TypeSig x _  -> srcLoc x
    C.Data x _ _   -> srcLoc x
    C.Record x _ _ -> srcLoc x
    C.FunDef x _ _ -> srcLoc x
    C.Open x       -> srcLoc x

instance HasSrcLoc C.Pattern where
  srcLoc p = case p of
    C.IdP x    -> srcLoc x
    C.AppP p _ -> srcLoc p
    C.HideP p  -> srcLoc p

