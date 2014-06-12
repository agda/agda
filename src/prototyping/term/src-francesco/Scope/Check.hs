{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}
module Scope.Check
    ( scopeCheck
    , ScopeError
    ) where

import Control.Arrow ((***), (&&&), first)
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
initScope = Scope $ Map.fromList []

type Hiding            = Int
type NumberOfArguments = Int

data NameInfo = VarName Name
              | DefName Name Hiding
              | ConName Name Hiding NumberOfArguments
              | ProjName Name Hiding

infoName :: NameInfo -> Name
infoName (VarName x)     = x
infoName (DefName x _)   = x
infoName (ConName x _ _) = x
infoName (ProjName x _)  = x

infoStringName :: NameInfo -> String
infoStringName i = s
  where Name _ s = infoName i

infoHiding :: NameInfo -> Hiding
infoHiding (VarName _)     = 0
infoHiding (DefName _ n)   = n
infoHiding (ConName _ n _) = n
infoHiding (ProjName _ n)  = n

instance HasSrcLoc NameInfo where
  srcLoc i = case i of
    VarName x     -> srcLoc x
    DefName x _   -> srcLoc x
    ConName x _ _ -> srcLoc x
    ProjName x _  -> srcLoc x

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

reservedNames = ["_", "Set", "refl", "J"]

impossible err = fail $ "impossible: " ++ err

mkName :: Int -> Int -> String -> Name
mkName l c s = Name (SrcLoc l c) s

mkVarInfo :: C.Name -> NameInfo
mkVarInfo (C.Name ((l, c), s)) = VarName (mkName l c s)

mkDefInfo :: C.Name -> Hiding -> NameInfo
mkDefInfo (C.Name ((l, c), s)) = DefName (mkName l c s)

mkConInfo :: C.Name -> Hiding -> NumberOfArguments -> NameInfo
mkConInfo (C.Name ((l, c), s)) = ConName (mkName l c s)

mkProjInfo :: C.Name -> Hiding -> NameInfo
mkProjInfo (C.Name ((l, c), s)) = ProjName (mkName l c s)

resolveName'' :: C.Name -> Check (Maybe NameInfo)
resolveName'' (C.Name ((l, c), s))
  | elem s reservedNames = impossible "reserved names should not end up in resolveName"
  | otherwise = asks $ Map.lookup s . inScope

resolveName' :: C.Name -> Check NameInfo
resolveName' x@(C.Name ((l, c), s)) = do
  mi <- resolveName'' x
  case mi of
    Nothing -> scopeError x $ "Not in scope: " ++ printTree x
    Just (VarName _)     -> return (VarName y)
    Just (DefName _ n)   -> return (DefName y n)
    Just (ConName _ n a) -> return (ConName y n a)
    Just (ProjName _ n)  -> return (ProjName y n)
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
scopeCheck (C.Prog _ ds) = flip runReaderT initScope $ unCheck $ checkDecls ds

isSet :: C.Name -> Check ()
isSet (C.Name ((l, c), "Set")) = return ()
isSet e = scopeError e "The type of a datatype or record should be Set"

isDefHead :: Head -> String -> Check Name
isDefHead (Def x) _ = return x
isDefHead h err     = scopeError h err

resolveDef :: C.Name -> Check (Name, Hiding)
resolveDef x = do
  i <- resolveName' x
  case i of
    DefName x n -> return (x, n)
    _ -> scopeError x $ show x ++ " should be a defined name."

resolveCon :: C.Name -> Check (Name, Hiding, NumberOfArguments)
resolveCon x = do
  i <- resolveName' x
  case i of
    ConName c n args -> return (c, n, args)
    _                -> scopeError x $ printTree x ++ " should be a constructor"

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

checkDecls :: [C.Decl] -> Check [Decl]
checkDecls ds0 = case ds0 of
  [] ->
    return []
  C.Postulate ds1 : ds2 ->
    checkDecls (ds1 ++ ds2)
  C.TypeSig x e : ds -> do
    (n, a) <- checkScheme e
    bindName (mkDefInfo x n) $ \x -> (TypeSig (Sig x a) :) <$> checkDecls ds
  C.Data x pars (C.NoDataBody set) : ds | Just ps <- isParamDecl pars -> do
    dataOrRecDecl x ps set ds
  C.Record x pars (C.NoRecordBody set) : ds | Just ps <- isParamDecl pars -> do
    dataOrRecDecl x ps set ds
  C.Data x pars (C.DataBody cs) : ds | Just xs <- isParamDef pars -> do
    (x, n) <- resolveDef x
    when (n > length xs) $ scopeError x $ "Too few parameters to " ++ show x ++
                                          " (implicit arguments must be explicitly bound here)"
    xs <- checkHiddenNames n xs
    let is = map mkVarInfo xs
    xs <- mapC bindName is $ return
    let t = App (Def x) (map (\x -> Apply (App (Var x) [])) xs)
    mapC (checkConstructor t is) cs $ \cs -> (DataDef x xs cs :) <$> checkDecls ds
  C.Record x pars (C.RecordBody con fs) : ds | Just xs <- isParamDef pars -> do
    (x, n) <- resolveDef x
    when (n > length xs) $ scopeError x $ "Too few parameters to " ++ show x ++
                                          " (implicit arguments must be explicitly bound here)"
    xs <- checkHiddenNames n xs
    let is = map mkVarInfo xs
    xs <- mapC bindName is $ return
    checkFields is (getFields fs) $ \fs ->
      bindName (mkConInfo con 0 (length fs)) $ \con ->
        (RecDef x xs con fs :) <$> checkDecls ds
  (d@C.Data{} : _) ->
    scopeError d $ "Bad data declaration"
  (d@C.Record{} : _) ->
    scopeError d $ "Bad record declaration"
  C.FunDef f _ _ : _ -> do
    let (clauses, ds) = takeFunDefs f ds0
    (f, n) <- resolveDef f
    clauses <- forM clauses $ \(ps, b) -> do
      ps     <- insertImplicitPatterns (srcLoc f) n ps
      (ps, b) <- mapC checkPattern ps $ \ps -> (,) ps <$> checkExpr b
      return $ Clause ps b
    (FunDef f clauses :) <$> checkDecls ds
  C.Open x : ds -> do
    resolveDef x
    checkDecls ds
  C.Import{} : ds -> do
    checkDecls ds
  where
    dataOrRecDecl x ps set ds = do
      isSet set
      (n, a) <- checkScheme (C.Pi (C.Tel ps) (C.App [C.Arg $ C.Id set]))
      bindName (mkDefInfo x n) $ \x -> (TypeSig (Sig x a) :) <$> checkDecls ds

    takeFunDefs :: C.Name -> [C.Decl] -> ([([C.Pattern], C.Expr)], [C.Decl])
    takeFunDefs f [] =
      ([], [])
    takeFunDefs f (C.FunDef f' ps b : ds) | sameName f f' =
      first ((ps, b) :) $ takeFunDefs f ds
    takeFunDefs _ d =
      ([], d)

    sameName (C.Name (_, f1)) (C.Name (_, f2)) = f1 == f2

checkFields :: [NameInfo] -> [C.Constr] -> CCheck [TypeSig]
checkFields ps fs ret = mapC bindName ps $ \_ -> do
  fs <- mapC (checkField ps) fs return
  mapC bindField fs ret
  where
    bindField :: (C.Name, Int, Expr) -> CCheck TypeSig
    bindField (x, n, a) ret = bindName (mkProjInfo x n) $ \x -> ret (Sig x a)

checkField :: [NameInfo] -> C.Constr -> CCheck (C.Name, Int, Expr)
checkField xs (C.Constr c e) ret =
  mapC bindName xs $ \_ -> do
    (n, a) <- checkScheme e
    bindName (mkVarInfo c) $ \_ -> ret (c, n, a)

getFields :: C.Fields -> [C.Constr]
getFields C.NoFields    = []
getFields (C.Fields fs) = fs

checkConstructor :: Expr -> [NameInfo] -> C.Constr -> CCheck TypeSig
checkConstructor d xs (C.Constr c e) ret =
  mapC bindName xs $ \_ -> do
    (n, a) <- checkScheme e
    args   <- checkConstructorType a d (map infoName xs)
    bindName (mkConInfo c n args) $ \c -> ret (Sig c a)

checkScheme :: C.Expr -> Check (Hiding, Expr)
checkScheme e = do
  (n, e) <- checkHiding e
  a      <- checkExpr e
  return (n, a)

checkConstructorType :: Expr
                        -- ^ The constructor's type.
                     -> Expr
                        -- ^ The data type applied to its parameters.
                     -> [Name]
                        -- ^ The parameters.
                     -> Check NumberOfArguments
                        -- ^ The number of constructor arguments is
                        -- returned.
checkConstructorType a d xs = check a
  where
  check (Fun _ b)  = succ <$> check b
  check (Pi x _ b) = do
    when (x `elem` xs) $
      scopeError a $ "Attempt to shadow data type parameter " ++ show x
    succ <$> check b
  check b
    | b == d    = return 0
    | otherwise = scopeError a $
                    "Not a well-formed constructor type: " ++ show a

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
      (c, n, args) <- resolveCon c
      ps <- insertImplicitPatterns (srcLoc c) n ps
      checkNumberOfConstructorArguments p c ps args
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
                doProj x e . map Apply =<< checkArgs e n es (\ _ -> return ())
            IsRefl p | [] <- es ->
              return $ Refl p
            IsRefl p ->
              scopeError p $ "refl applied to arguments " ++ show es
            IsCon c args -> do
              Con c <$> checkArgs z n es
                        (\es -> checkNumberOfConstructorArguments e c es args)
            Other h    -> App h . map Apply <$> checkArgs z n es (\ _ -> return ())
            HeadSet p  -> return $ Set p
            HeadMeta p -> return $ Meta p
    doProj x (App h es1) es2 = return $ App h (es1 ++ [Proj x] ++ es2)
    doProj x e _ = scopeError x $ "Cannot project " ++ show x ++ " from " ++ show e

checkArgs :: HasSrcLoc a =>
             a -> Hiding -> [C.Arg] -> (forall b. [b] -> Check ()) ->
             Check [Expr]
checkArgs x n es extraCheck = do
  es <- insertImplicit (srcLoc x) n es
  extraCheck es
  mapM checkExpr es

checkNumberOfConstructorArguments ::
  HasSrcLoc e => e -> Name -> [a] -> NumberOfArguments -> Check ()
checkNumberOfConstructorArguments loc c as args = do
  when (nas < args) $
    scopeError loc $ "The constructor " ++ show c ++
                     " is applied to too few arguments."
  when (nas > args) $
    scopeError loc $ "The constructor " ++ show c ++
                     " is applied to too many arguments."
  where nas = length as

data AppHead = IsProj Name
             | IsCon Name NumberOfArguments
             | IsRefl SrcLoc
             | Other Head
             | HeadSet SrcLoc
             | HeadMeta SrcLoc

instance HasSrcLoc AppHead where
  srcLoc h = case h of
    IsProj x   -> srcLoc x
    IsCon c _  -> srcLoc c
    IsRefl p   -> p
    Other h    -> srcLoc h
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
checkAppHead (C.Name ((l, c), "_"))    = return (HeadMeta $ SrcLoc l c, 0)
checkAppHead (C.Name ((l, c), "Set"))  = return (HeadSet $ SrcLoc l c, 0)
checkAppHead (C.Name ((l, c), "J"))    = return (Other (J (SrcLoc l c)), 3)
checkAppHead (C.Name ((l, c), "refl")) = return (IsRefl (SrcLoc l c), 0)
checkAppHead x = do
  i <- resolveName' x
  case i of
    ProjName x n  -> return (IsProj x, n)
    VarName x     -> return (Other $ Var x, 0)
    ConName x n a -> return (IsCon x a, n)
    DefName x n   -> return (Other $ Def x, n)

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
    C.Postulate (d:ds) -> srcLoc d
    C.Postulate []     -> noSrcLoc
    C.TypeSig x _      -> srcLoc x
    C.Data x _ _       -> srcLoc x
    C.Record x _ _     -> srcLoc x
    C.FunDef x _ _     -> srcLoc x
    C.Open x           -> srcLoc x
    C.Import x         -> srcLoc x

instance HasSrcLoc C.Pattern where
  srcLoc p = case p of
    C.IdP x    -> srcLoc x
    C.AppP p _ -> srcLoc p
    C.HideP p  -> srcLoc p
