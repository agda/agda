{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances #-}

{-| Translation from "Syntax.Concrete" to "Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Syntax.Translation.ConcreteToAbstract
    ( ToAbstract(..), localToAbstract
    , concreteToAbstract_
    , concreteToAbstract
    , NewModuleQName(..)
    , OldName(..)
    , TopLevel(..)
    , TopLevelInfo(..)
    ) where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Control.Monad.Error hiding (mapM)
import Data.Typeable
import Data.Traversable (mapM)
import Data.List ((\\), nub)

import Syntax.Concrete as C
import Syntax.Abstract as A
import Syntax.Position
import Syntax.Common
import Syntax.Info
import Syntax.Concrete.Definitions as C
import Syntax.Concrete.Operators
import Syntax.Fixity
import Syntax.Scope.Base
import Syntax.Scope.Monad
import Syntax.Strict

import TypeChecking.Monad.Base (TypeError(..), Call(..), typeError, TCErr(..))
import TypeChecking.Monad.Trace (traceCall, traceCallCPS)
import TypeChecking.Monad.State
import TypeChecking.Monad.Options

#ifndef __HADDOCK__
import {-# SOURCE #-} Interaction.Imports (scopeCheckImport)
#endif

import Utils.Monad
import Utils.Tuple

#include "../../undefined.h"


{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

notAModuleExpr e	    = typeError $ NotAModuleExpr e
notAnExpression e	    = typeError $ NotAnExpression e
notAValidLetBinding d	    = typeError $ NotAValidLetBinding d
nothingAppliedToHiddenArg e = typeError $ NothingAppliedToHiddenArg e

-- Debugging

printLocals :: Int -> String -> ScopeM ()
printLocals v s = verboseS "scope.top" v $ do
  locals <- scopeLocals <$> getScope
  liftIO $ putStrLn $ s ++ " " ++ show locals

printScope :: Int -> String -> ScopeM ()
printScope v s = verboseS "scope.top" v $ do
  scope <- getScope
  liftIO $ putStrLn $ s ++ " " ++ show scope

{--------------------------------------------------------------------------
    Helpers
 --------------------------------------------------------------------------}

lhsArgs :: C.Pattern -> (C.Name, [NamedArg C.Pattern])
lhsArgs p = case appView p of
    Arg _ (Named _ (IdentP (C.QName x))) : ps -> (x, ps)
    _				              -> __IMPOSSIBLE__
    where
	mkHead	  = Arg NotHidden . unnamed
	notHidden = Arg NotHidden . unnamed
	appView p = case p of
	    AppP p arg	  -> appView p ++ [arg]
	    OpAppP _ x ps -> mkHead (IdentP $ C.QName x) : map notHidden ps
	    ParenP _ p	  -> appView p
	    RawAppP _ _	  -> __IMPOSSIBLE__
	    _		  -> [ mkHead p ]

makeSection :: ModuleInfo -> A.ModuleName -> A.Telescope -> [A.Declaration] -> [A.Declaration]
makeSection info m tel ds = [A.Section info m tel ds]

annotateDecl :: A.Declaration -> ScopeM A.Declaration
annotateDecl d = annotateDecls [d]

annotateDecls :: [A.Declaration] -> ScopeM A.Declaration
annotateDecls ds = do
  s <- getScope
  return $ ScopedDecl s ds

annotateExpr :: A.Expr -> ScopeM A.Expr
annotateExpr e = do
  s <- getScope
  return $ ScopedExpr s e

expandEllipsis :: C.Pattern -> [C.Pattern] -> C.Clause -> C.Clause
expandEllipsis _ _ c@(C.Clause _ (C.LHS _ _ _) _ _ _) = c
expandEllipsis p ps (C.Clause x (C.Ellipsis _ ps' es) rhs wh wcs) =
  C.Clause x (C.LHS p (ps ++ ps') es) rhs wh wcs

-- | Make sure that each variable occurs only once.
checkPatternLinearity :: [A.Pattern' e] -> ScopeM ()
checkPatternLinearity ps = case xs \\ nub xs of
    []	-> return ()
    ys	-> typeError $ RepeatedVariablesInPattern $ nub ys
  where
    xs = concatMap vars ps
    vars :: A.Pattern' e -> [C.Name]
    vars p = case p of
      A.VarP x	      -> [nameConcrete x]
      A.ConP _ _ args -> concatMap (vars . namedThing . unArg) args
      A.WildP _	      -> []
      A.AsP _ x p     -> nameConcrete x : vars p
      A.DotP _ _      -> []
      A.AbsurdP _     -> []
      A.LitP _	      -> []
      A.DefP _ _ args -> __IMPOSSIBLE__
      A.ImplicitP _   -> __IMPOSSIBLE__

-- | Compute the type of the record constructor (with bogus target type)
recordConstructorType :: [NiceDeclaration] -> C.Expr
recordConstructorType fields = build fs
  where
    fs = reverse $ dropWhile notField $ reverse fields

    notField NiceField{} = False
    notField _           = True

    build (NiceField r f _ _ x e : fs) = C.Pi [C.TypedBindings r NotHidden
                                                [C.TBind r [BName x f] e]
                                              ] $ build fs
      where r = getRange x
    build (d : fs)                     = C.Let noRange (notSoNiceDeclarations [d]) $ build fs
    build []                           = C.Prop noRange

checkModuleMacro apply r p a x tel m args open dir =
    withLocalVars $ do
    tel' <- toAbstract tel
    (x',m1,args') <- toAbstract ( NewModuleName x
                                , OldModuleName m
                                , args
                                )
    printScope 20 "module macro"
    pushScope x'
    m0 <- getCurrentModule
    openModule_ m $ dir { C.publicOpen = True }
    printScope 20 "opened source module"
    s : _ <- scopeStack <$> getScope
    (renD, renM) <- renamedCanonicalNames m1 m0 s
    modifyTopScope $ renameCanonicalNames renD renM
    printScope 20 "renamed stuff"
    popScope p
    printScope 20 "popped"
    bindModule p x m0
    case open of
      DontOpen -> return ()
      DoOpen   -> openModule_ (C.QName x) $ defaultImportDir { C.publicOpen = C.publicOpen dir }
    printScope 20 $ case open of
      DontOpen  -> "didn't open"
      DoOpen    -> "opened"
    printScope 10 $ "before stripping"
    stripNoNames
    printScope 10 $ "after stripping"
    return [ apply info m0 tel' m1 args' renD renM ]
  where
    info = mkRangedModuleInfo p a r

{--------------------------------------------------------------------------
    Translation
 --------------------------------------------------------------------------}

concreteToAbstract_ :: ToAbstract c a => c -> ScopeM a
concreteToAbstract_ x = toAbstract x

concreteToAbstract :: ToAbstract c a => ScopeInfo -> c -> ScopeM a
concreteToAbstract scope x = withScope_ scope (toAbstract x)

-- | Things that can be translated to abstract syntax are instances of this
--   class.
class ToAbstract concrete abstract | concrete -> abstract where
    toAbstract	  :: concrete -> ScopeM abstract

-- | This function should be used instead of 'toAbstract' for things that need
--   to keep track of precedences to make sure that we don't forget about it.
toAbstractCtx :: ToAbstract concrete abstract =>
		 Precedence -> concrete -> ScopeM abstract
toAbstractCtx ctx c = withContextPrecedence ctx $ toAbstract c

setContextCPS :: Precedence -> (a -> ScopeM b) ->
		 ((a -> ScopeM b) -> ScopeM b) -> ScopeM b
setContextCPS p ret f = do
  p' <- getContextPrecedence
  withContextPrecedence p $ f $ withContextPrecedence p' . ret

localToAbstractCtx :: ToAbstract concrete abstract =>
		     Precedence -> concrete -> (abstract -> ScopeM a) -> ScopeM a
localToAbstractCtx ctx c ret = setContextCPS ctx ret (localToAbstract c)

-- | This operation does not affect the scope, i.e. the original scope
--   is restored upon completion.
localToAbstract :: ToAbstract c a => c -> (a -> ScopeM b) -> ScopeM b
localToAbstract x ret = fst <$> localToAbstract' x ret

-- | Like 'localToAbstract' but returns the scope after the completion of the
--   second argument.
localToAbstract' :: ToAbstract c a => c -> (a -> ScopeM b) -> ScopeM (b, ScopeInfo)
localToAbstract' x ret = do
  scope <- getScope
  withScope scope $ ret =<< toAbstract x

instance (ToAbstract c1 a1, ToAbstract c2 a2) => ToAbstract (c1,c2) (a1,a2) where
  toAbstract (x,y) =
    (,) <$> toAbstract x <*> toAbstract y

instance (ToAbstract c1 a1, ToAbstract c2 a2, ToAbstract c3 a3) =>
	 ToAbstract (c1,c2,c3) (a1,a2,a3) where
    toAbstract (x,y,z) = flatten <$> toAbstract (x,(y,z))
	where
	    flatten (x,(y,z)) = (x,y,z)

instance ToAbstract c a => ToAbstract [c] [a] where
    toAbstract = mapM toAbstract 

instance ToAbstract c a => ToAbstract (Maybe c) (Maybe a) where
    toAbstract Nothing  = return Nothing
    toAbstract (Just x) = Just <$> toAbstract x

-- Names ------------------------------------------------------------------

newtype NewName a = NewName a
newtype OldQName  = OldQName C.QName
newtype OldName   = OldName C.Name
newtype PatName   = PatName C.QName

instance ToAbstract (NewName C.Name) A.Name where
  toAbstract (NewName x) = do
    y <- freshAbstractName_ x
    bindVariable x y
    return y

instance ToAbstract (NewName C.BoundName) A.Name where
  toAbstract (NewName (BName x fx)) = do
    y <- freshAbstractName fx x
    bindVariable x y
    return y

nameExpr :: AbstractName -> A.Expr
nameExpr d = mk (anameKind d) $ anameName d
  where
    mk DefName = Def
    mk ConName = Con . (:[])

instance ToAbstract OldQName A.Expr where
  toAbstract (OldQName x) = do
    qx <- resolveName x
    case qx of
      VarName x'         -> return $ A.Var x'
      DefinedName d      -> return $ nameExpr d
      ConstructorName ds -> return $ A.Con (map anameName ds)
      UnknownName        -> notInScope x

data APatName = VarPatName A.Name
	      | ConPatName [AbstractName]

instance ToAbstract PatName APatName where
  toAbstract (PatName x) = do
    reportLn 10 $ "checking pattern name: " ++ show x
    rx <- resolveName x
    z  <- case (rx, x) of
      -- TODO: warn about shadowing
      (VarName y,     C.QName x)			  -> return $ Left x -- typeError $ RepeatedVariableInPattern y x
      (DefinedName d, C.QName x) | DefName == anameKind d -> return $ Left x
      (UnknownName,   C.QName x)			  -> return $ Left x
      (ConstructorName ds, _)	                          -> return $ Right ds
      _							  -> fail $ "not a constructor: " ++ show x -- TODO
    case z of
      Left x  -> do
	reportLn 10 $ "it was a var: " ++ show x
	p <- VarPatName <$> toAbstract (NewName x)
	printLocals 10 "bound it:"
	return p
      Right cs -> do
	reportLn 10 $ "it was a con: " ++ show (map anameName cs)
	return $ ConPatName cs

-- Should be a defined name.
instance ToAbstract OldName A.QName where
  toAbstract (OldName x) = do
    rx <- resolveName (C.QName x)
    case rx of
      DefinedName d -> return $ anameName d
      _		    -> __IMPOSSIBLE__

newtype NewModuleName  = NewModuleName  C.Name
newtype NewModuleQName = NewModuleQName C.QName
newtype OldModuleName  = OldModuleName  C.QName

instance ToAbstract NewModuleName A.ModuleName where
  toAbstract (NewModuleName x) = mnameFromList . (:[]) <$> freshAbstractName_ x

instance ToAbstract NewModuleQName A.ModuleName where
  toAbstract (NewModuleQName q) =
    foldr1 A.qualifyM <$> mapM (toAbstract . NewModuleName) (toList q)
    where
      toList (C.QName  x) = [x]
      toList (C.Qual m x) = m : toList x

instance ToAbstract OldModuleName A.ModuleName where
  toAbstract (OldModuleName q) = amodName <$> resolveModule q

-- Expressions ------------------------------------------------------------

-- | Peel off 'C.HiddenArg' and represent it as an 'NamedArg'.
mkNamedArg :: C.Expr -> NamedArg C.Expr
mkNamedArg (C.HiddenArg _ e) = Arg Hidden e
mkNamedArg e		     = Arg NotHidden $ unnamed e

-- | Peel off 'C.HiddenArg' and represent it as an 'Arg', throwing away any name.
mkArg :: C.Expr -> Arg C.Expr
mkArg (C.HiddenArg _ e) = Arg Hidden $ namedThing e
mkArg e			= Arg NotHidden e

instance ToAbstract C.Expr A.Expr where
  toAbstract e =
    traceCall (ScopeCheckExpr e) $ annotateExpr =<< case e of
  -- Names
      Ident x -> toAbstract (OldQName x)

  -- Literals
      C.Lit l -> return $ A.Lit l

  -- Meta variables
      C.QuestionMark r n -> do
	scope <- getScope
	return $ A.QuestionMark $ MetaInfo
		    { metaRange  = r
		    , metaScope  = scope
		    , metaNumber = n
		    }
      C.Underscore r n -> do
	scope <- getScope
	return $ A.Underscore $ MetaInfo
		    { metaRange  = r
		    , metaScope  = scope
		    , metaNumber = n
		    }

  -- Raw application
      C.RawApp r es -> do
	e <- parseApplication es
	toAbstract e

  -- Application
      C.App r e1 e2 -> do
	e1 <- toAbstractCtx FunctionCtx e1
	e2 <- toAbstractCtx ArgumentCtx e2
	return $ A.App (ExprRange r) e1 e2

  -- Operator application
      C.OpApp r op es -> toAbstractOpApp r op es

  -- With application
      C.WithApp r e es -> do
	e : es <- mapM (toAbstractCtx WithAppCtx) (e : es)
	return $ A.WithApp (ExprRange r) e es

  -- Malplaced hidden argument
      C.HiddenArg _ _ -> nothingAppliedToHiddenArg e

  -- Lambda
      e0@(C.Lam r bs e) -> do
	localToAbstract bs $ \(b:bs') -> do
	e	 <- toAbstractCtx TopCtx e
	let info = ExprRange r
	return $ A.Lam info b $ foldr mkLam e bs'
	where
	    mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

  -- Function types
      C.Fun r e1 e2 -> do
	e1 <- toAbstractCtx FunctionSpaceDomainCtx $ mkArg e1
	e2 <- toAbstractCtx TopCtx e2
	let info = ExprRange r
	return $ A.Fun info e1 e2

      e0@(C.Pi tel e) ->
	localToAbstract tel $ \tel -> do
	e    <- toAbstractCtx TopCtx e
	let info = ExprRange (getRange e0)
	return $ A.Pi info tel e

  -- Sorts
      C.Set _    -> return $ A.Set (ExprRange $ getRange e) 0
      C.SetN _ n -> return $ A.Set (ExprRange $ getRange e) n
      C.Prop _   -> return $ A.Prop $ ExprRange $ getRange e

  -- Let
      e0@(C.Let _ ds e) ->
	localToAbstract (LetDefs ds) $ \ds' -> do
	e	 <- toAbstractCtx TopCtx e
	let info = ExprRange (getRange e0)
	return $ A.Let info ds' e

  -- Record construction
      C.Rec r fs  -> do
	let (xs, es) = unzip fs
	es <- toAbstractCtx TopCtx es
	return $ A.Rec (ExprRange r) $ zip xs es

  -- Parenthesis
      C.Paren _ e -> toAbstractCtx TopCtx e

  -- Pattern things
      C.As _ _ _ -> notAnExpression e
      C.Dot _ _  -> notAnExpression e
      C.Absurd _ -> notAnExpression e

instance ToAbstract C.LamBinding A.LamBinding where
  toAbstract (C.DomainFree h x) = A.DomainFree h <$> toAbstract (NewName x)
  toAbstract (C.DomainFull tb)	= A.DomainFull <$> toAbstract tb

instance ToAbstract C.TypedBindings A.TypedBindings where
  toAbstract (C.TypedBindings r h bs) = A.TypedBindings r h <$> toAbstract bs

instance ToAbstract C.TypedBinding A.TypedBinding where
  toAbstract (C.TBind r xs t) = do
    t' <- toAbstractCtx TopCtx t
    xs' <- toAbstract (map NewName xs)
    return $ A.TBind r xs' t'
  toAbstract (C.TNoBind e) = do
    e <- toAbstractCtx TopCtx e
    return (A.TNoBind e)

newtype TopLevel a = TopLevel a

-- | Returns the scope inside the checked module.
scopeCheckModule :: Range -> Access -> IsAbstract -> C.QName -> A.ModuleName -> C.Telescope -> [C.Declaration] ->
		    ScopeM (ScopeInfo, [A.Declaration])
scopeCheckModule r a c x m tel ds = do
  pushScope m
  qm <- getCurrentModule
  ds <- withLocalVars $ do
	  tel <- toAbstract tel
	  makeSection info qm tel <$> toAbstract ds
  scope <- getScope
  popScope a
  bindQModule a x qm
  return (scope, ds)
  where
    info = mkRangedModuleInfo a c r

data TopLevelInfo = TopLevelInfo
	{ topLevelDecls :: [A.Declaration]
	, outsideScope  :: ScopeInfo
	, insideScope	:: ScopeInfo
	}

-- Top-level declarations are always (import|open)* module
instance ToAbstract (TopLevel [C.Declaration]) TopLevelInfo where
    toAbstract (TopLevel ds) = case splitAt (length ds - 1) ds of
	(ds', [C.Module r m tel ds]) -> do
	  setTopLevelModule m
	  am	       <- toAbstract (NewModuleQName m)
	  ds'	       <- toAbstract ds'
	  (scope0, ds) <- scopeCheckModule r PublicAccess ConcreteDef m am tel ds
	  scope	       <- getScope
	  return $ TopLevelInfo (ds' ++ ds) scope scope0
	_ -> __IMPOSSIBLE__


niceDecls :: [C.Declaration] -> ScopeM [NiceDeclaration]
niceDecls ds = case runNice $ niceDeclarations ds of
  Left e   -> throwError $ Exception (getRange e) (show e)
  Right ds -> return ds

instance ToAbstract [C.Declaration] [A.Declaration] where
  toAbstract ds = toAbstract =<< niceDecls ds

newtype LetDefs = LetDefs [C.Declaration]
newtype LetDef = LetDef NiceDeclaration

instance ToAbstract LetDefs [A.LetBinding] where
    toAbstract (LetDefs ds) =
	concat <$> (toAbstract =<< map LetDef <$> niceDecls ds)

instance ToAbstract LetDef [A.LetBinding] where
    toAbstract (LetDef d) =
	case d of
	    NiceDef _ c [C.Axiom _ _ _ _ x t] [C.FunDef _ _ _ _ _ _ [cl]] ->
		do  e <- letToAbstract cl
		    t <- toAbstract t
		    x <- toAbstract (NewName x)
		    return [ A.LetBind (LetSource c) x t e ]

            -- You can't open public in a let
            NiceOpen r x dirs | not (C.publicOpen dirs) -> do
              current <- getCurrentModule
              m	      <- toAbstract (OldModuleName x)
              n	      <- length . scopeLocals <$> getScope
              openModule_ x dirs
              return []

            NiceModuleMacro r p a x tel e open dir | not (C.publicOpen dir) -> case appView e of
              AppView (Ident m) args -> checkModuleMacro LetApply r p a x tel m args open dir
              _                      -> notAModuleExpr e

	    _	-> notAValidLetBinding d
	where
	    letToAbstract (C.Clause top clhs@(C.LHS p [] []) (C.RHS rhs) NoWhere []) = do
		p    <- parseLHS (Just top) p
		localToAbstract (snd $ lhsArgs p) $ \args ->
		    do	rhs <- toAbstract rhs
			foldM lambda rhs (reverse args)  -- just reverse because these DomainFree
	    letToAbstract _ = notAValidLetBinding d

	    -- Named patterns not allowed in let definitions
	    lambda e (Arg h (Named Nothing (A.VarP x))) = return $ A.Lam i (A.DomainFree h x) e
		where
		    i = ExprRange (fuseRange x e)
	    lambda e (Arg h (Named Nothing (A.WildP i))) =
		do  x <- freshNoName (getRange i)
		    return $ A.Lam i' (A.DomainFree h x) e
		where
		    i' = ExprRange (fuseRange i e)
	    lambda _ _ = notAValidLetBinding d

instance ToAbstract C.Pragma [A.Pragma] where
    toAbstract (C.OptionsPragma _ opts) = return [ A.OptionsPragma opts ]
    toAbstract (C.CompiledDataPragma _ x hcs) = do
      e <- toAbstract $ OldQName x
      case e of
        A.Def x -> return [ A.CompiledDataPragma x hcs ]
        _       -> fail $ "Not a datatype: " ++ show x  -- TODO: error message
    toAbstract (C.CompiledPragma _ x hs) = do
      e <- toAbstract $ OldQName x
      y <- case e of
            A.Def x -> return x
            A.Con _ -> fail "Use HASKELL_DATA for constructors" -- TODO
            _       -> __IMPOSSIBLE__
      return [ A.CompiledPragma y hs ]
    toAbstract (C.BuiltinPragma _ b e) = do
	e <- toAbstract e
	return [ A.BuiltinPragma b e ]
    toAbstract (C.LinePragma _ _ _) = return []
    toAbstract (C.ImportPragma _ i) = do
      addHaskellImport i
      return []

-- Only constructor names are bound by definitions.
instance ToAbstract NiceDefinition Definition where

    -- Function definitions
    toAbstract d@(C.FunDef r ds f p a x cs) =
      traceCall (ScopeCheckDefinition d) $ do
        (x',cs') <- toAbstract (OldName x,cs)
	return $ A.FunDef (mkSourcedDefInfo x f p a ds) x' cs'

    -- Data definitions
    toAbstract d@(C.DataDef r f p a x pars cons) =
      traceCall (ScopeCheckDefinition d) $
      withLocalVars $ do
	pars <- toAbstract pars
	cons <- toAbstract (map Constr cons)
	x'   <- toAbstract (OldName x)
	return $ A.DataDef (mkRangedDefInfo x f p a r) x' pars cons

    -- Record definitions (mucho interesting)
    toAbstract d@(C.RecDef r f p a x pars fields) =
      traceCall (ScopeCheckDefinition d) $
      withLocalVars $ do
	pars   <- toAbstract pars
	x'     <- toAbstract (OldName x)
        contel <- toAbstract $ recordConstructorType fields
	let m = mnameFromList $ (:[]) $ last $ qnameToList x'
	printScope 15 "before record"
	pushScope m
	afields <- toAbstract fields
	printScope 15 "checked fields"
	qm <- getCurrentModule
	popScope p
	bindModule p x qm
	printScope 15 "record complete"
	return $ A.RecDef (mkRangedDefInfo x f p a r) x' pars contel afields

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list.
instance ToAbstract NiceDeclaration A.Declaration where

  toAbstract d = (=<<) annotateDecls $
    traceCall (ScopeCheckDeclaration d) $
    case d of

  -- Axiom
    C.Axiom r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Axiom (mkRangedDefInfo x f p a r) y t' ]

  -- Fields
    C.NiceField r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Field (mkRangedDefInfo x f p a r) y t' ]

  -- Primitive function
    PrimitiveFunction r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Primitive (mkRangedDefInfo x f p a r) y t' ]

  -- Definitions (possibly mutual)
    NiceDef r cs ts ds -> do
      (ts', ds') <- toAbstract (ts, ds)
      return [ Definition (DeclInfo C.noName_ $ DeclRange r) ts' ds' ]
			  -- TODO: what does the info mean here?

  -- TODO: what does an abstract module mean? The syntax doesn't allow it.
    NiceModule r p a name tel ds -> do
      aname <- toAbstract (NewModuleQName name)
      snd <$> scopeCheckModule r p a name aname tel ds

    NiceModuleMacro r p a x tel e open dir -> case appView e of
      AppView (Ident m) args -> checkModuleMacro Apply r p a x tel m args open dir
      _                      -> notAModuleExpr e

    NiceOpen r x dir -> do
      current <- getCurrentModule
      m	      <- toAbstract (OldModuleName x)
      n	      <- length . scopeLocals <$> getScope

      printScope 20 $ "opening " ++ show x
      -- Opening (privately) a submodule or opening into a non-parameterised module
      -- is fine. Otherwise we have to create a temporary module.
      if not (C.publicOpen dir) -- && (m `isSubModuleOf` current || n == 0)
	then do
	  reportLn 20 "normal open"
	  openModule_ x dir
	  printScope 20 $ "result:"
	  return []
	else do
	  reportLn 20 "fancy open"
	  tmp <- nameConcrete <$> freshNoName (getRange x)
	  d   <- toAbstract $ NiceModuleMacro r PrivateAccess ConcreteDef
					    tmp [] (C.Ident x) DoOpen dir
	  printScope 20 "result:"
	  return [d]

    NicePragma r p -> do
      ps <- toAbstract p
      return $ map (A.Pragma r) ps

    NiceImport r x as open dir -> do

      -- First scope check the imported module and return its name and
      -- interface. This is done with that module as the top-level module.
      (m, i) <- withTopLevelModule x $ do
	m <- toAbstract $ NewModuleQName x
	printScope 10 "before import:"
	i <- scopeCheckImport m
	printScope 10 $ "scope checked import: " ++ show i
	return (m, i)

      -- Abstract name for the imported module.
      m' <- case as of
	      Nothing -> return m
	      Just y  -> toAbstract $ NewModuleName y

      -- Now, we push a new scope with the name we want for the imported
      -- module containing its interface. We then do a public open on the
      -- imported module and pop the scope. This results in the concrete names
      -- getting renamed to use the "as" name (if any).
      pushScope m'
      modifyTopScope (`mergeScope` setScopeAccess PrivateAccess i)
      openModule_ x $ dir { publicOpen = True }
      popScope PrivateAccess

      -- Finally we bind the desired module name to the right abstract name.
      bindQModule PrivateAccess name m

      printScope 10 "merged imported sig:"
      ds <- case open of
	DontOpen -> return []
	DoOpen   -> do
	  toAbstract [ C.Open r name dir { usingOrHiding = Hiding []
					 , renaming	 = []
					 }
		     ]
      return $ A.Import (mkRangedModuleInfo PublicAccess ConcreteDef r) m : ds
      where
	  name = maybe x C.QName as

newtype Constr a = Constr a

instance ToAbstract (Constr C.NiceDeclaration) A.Declaration where
    toAbstract (Constr (C.Axiom r f p a x t)) = do
	t' <- toAbstractCtx TopCtx t
	y  <- freshAbstractQName f x
	bindName p' ConName x y
	return $ A.Axiom (mkRangedDefInfo x f p a r) y t'
	where
	    -- An abstract constructor is private (abstract constructor means
	    -- abstract datatype, so the constructor should not be exported).
	    p' = case (a, p) of
		    (AbstractDef, _) -> PrivateAccess
		    (_, p)	     -> p

    toAbstract _ = __IMPOSSIBLE__    -- a constructor is always an axiom

instance ToAbstract C.Clause A.Clause where
    toAbstract (C.Clause top (C.Ellipsis _ _ _) _ _ _) = fail "bad '...'" -- TODO: errors message
    toAbstract (C.Clause top lhs@(C.LHS p wps with) rhs wh wcs) = withLocalVars $ do
      let wcs' = map (expandEllipsis p wps) wcs
      lhs' <- toAbstract (LeftHandSide top p wps)
      printLocals 10 "after lhs:"
      let (whname, whds) = case wh of
	    NoWhere	   -> (Nothing, [])
	    AnyWhere ds	   -> (Nothing, ds)
	    SomeWhere m ds -> (Just m, ds)
      case whds of
	[] -> do
	  rhs <- toAbstract =<< toAbstractCtx TopCtx (RightHandSide with wcs' rhs)
	  return $ A.Clause lhs' rhs []
	_	-> do
	  m <- C.QName <$> maybe (nameConcrete <$> freshNoName noRange) return whname
	  let acc = maybe PrivateAccess (const PublicAccess) whname  -- unnamed where's are private
	  let tel = []
	  am <- toAbstract (NewModuleQName m)
	  (scope, ds) <- scopeCheckModule (getRange wh) acc ConcreteDef m am tel whds
	  setScope scope
	  -- the right hand side is checked inside the module of the local definitions
	  rhs <- toAbstractCtx TopCtx (RightHandSide with wcs' rhs)
	  qm <- getCurrentModule
	  case acc of
	    PublicAccess  -> popScope PublicAccess
	    PrivateAccess -> popScope_	-- unnamed where clauses are not in scope
	  bindQModule acc m qm
          rhs <- toAbstract rhs
	  return $ A.Clause lhs' rhs ds

data RightHandSide = RightHandSide [C.Expr] [C.Clause] C.RHS
data AbstractRHS = AbsurdRHS'
                 | WithRHS' [A.Expr] [C.Clause]  -- ^ The with clauses haven't been translated yet
                 | RHS' A.Expr

instance ToAbstract AbstractRHS A.RHS where
  toAbstract AbsurdRHS'       = return A.AbsurdRHS
  toAbstract (RHS' e)         = return $ A.RHS e
  toAbstract (WithRHS' es cs) = A.WithRHS es <$> toAbstract cs

instance ToAbstract RightHandSide AbstractRHS where
  toAbstract (RightHandSide [] (_ : _) _)        = __IMPOSSIBLE__
  toAbstract (RightHandSide (_ : _) _ (C.RHS _)) = typeError $ BothWithAndRHS
  toAbstract (RightHandSide [] [] rhs)           = toAbstract rhs
  toAbstract (RightHandSide es cs C.AbsurdRHS) = do
    es <- toAbstractCtx TopCtx es
    return $ WithRHS' es cs

instance ToAbstract C.RHS AbstractRHS where
    toAbstract C.AbsurdRHS = return $ AbsurdRHS'
    toAbstract (C.RHS e)   = RHS' <$> toAbstract e

data LeftHandSide = LeftHandSide C.Name C.Pattern [C.Pattern]

instance ToAbstract LeftHandSide A.LHS where
    toAbstract (LeftHandSide top lhs wps) =
      traceCall (ScopeCheckLHS top lhs) $ do
	p <- parseLHS (Just top) lhs
	printLocals 10 "before lhs:"
        let (x, ps) = lhsArgs p
	x    <- toAbstract (OldName x)
	args <- toAbstract ps
	wps  <- toAbstract =<< mapM (parseLHS Nothing) wps
	checkPatternLinearity (map (namedThing . unArg) args ++ wps)
	printLocals 10 "checked pattern:"
	args <- toAbstract args -- take care of dot patterns
	wps  <- toAbstract wps
	printLocals 10 "checked dots:"
	return $ A.LHS (LHSRange $ getRange (lhs, wps)) x args wps

instance ToAbstract c a => ToAbstract (Arg c) (Arg a) where
    toAbstract (Arg h e) = Arg h <$> toAbstractCtx (hiddenArgumentCtx h) e

instance ToAbstract c a => ToAbstract (Named name c) (Named name a) where
    toAbstract (Named n e) = Named n <$> toAbstract e

-- Patterns are done in two phases. First everything but the dot patterns, and
-- then the dot patterns. This is because dot patterns can refer to variables
-- bound anywhere in the pattern.

instance ToAbstract c a => ToAbstract (A.Pattern' c) (A.Pattern' a) where
    toAbstract = mapM toAbstract

instance ToAbstract C.Pattern (A.Pattern' C.Expr) where

    toAbstract p@(C.IdentP x) = do
	px <- toAbstract (PatName x)
	case px of
	    VarPatName y  -> return $ VarP y
	    ConPatName ds -> return $ ConP (PatRange (getRange p)) (map anameName ds) []

    toAbstract p0@(AppP p q) = do
	(p', q') <- toAbstract (p,q)
	case p' of
	    ConP _ x as -> return $ ConP info x (as ++ [q'])
	    DefP _ x as -> return $ DefP info x (as ++ [q'])
	    _		-> typeError $ InvalidPattern p0
	where
	    r = getRange p0
	    info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    toAbstract p0@(OpAppP r op ps) = do
	p <- toAbstract (IdentP $ C.QName op)
	ps <- toAbstract ps
	case p of
	  ConP _ x as -> return $ ConP info x (as ++ map (Arg NotHidden . unnamed) ps)
	  DefP _ x as -> return $ DefP info x (as ++ map (Arg NotHidden . unnamed) ps)
	  _	      -> __IMPOSSIBLE__
	where
	    r = getRange p0
	    info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    -- Removed when parsing
    toAbstract (HiddenP _ _) = __IMPOSSIBLE__
    toAbstract (RawAppP _ _) = __IMPOSSIBLE__

    toAbstract p@(C.WildP r)    = return $ A.WildP (PatSource r $ const p)
    toAbstract (C.ParenP _ p)   = toAbstract p
    toAbstract (C.LitP l)	= return $ A.LitP l
    toAbstract p0@(C.AsP r x p) = do
	x <- toAbstract (NewName x)
	p <- toAbstract p
	return $ A.AsP info x p
	where
	    info = PatSource r $ \_ -> p0
    -- we have to do dot patterns at the end
    toAbstract p0@(C.DotP r e) = return $ A.DotP info e
	where info = PatSource r $ \_ -> p0
    toAbstract p0@(C.AbsurdP r) = return $ A.AbsurdP info
	where
	    info = PatSource r $ \_ -> p0

-- | Turn an operator application into abstract syntax. Make sure to record the
-- right precedences for the various arguments.
toAbstractOpApp :: Range -> C.Name -> [C.Expr] -> ScopeM A.Expr
toAbstractOpApp r op@(C.NoName _ _) es = __IMPOSSIBLE__
toAbstractOpApp r op@(C.Name _ xs) es = do
    f  <- getFixity (C.QName op)
    op <- toAbstract (OldQName $ C.QName op)
    foldl app op <$> left f xs es
    where
	app e arg = A.App (ExprRange (fuseRange e arg)) e
		  $ Arg NotHidden $ unnamed arg

	left f (Hole : xs) (e : es) = do
	    e  <- toAbstractCtx (LeftOperandCtx f) e
	    es <- inside f xs es
	    return (e : es)
	left f (Id {} : xs) es = inside f xs es
	left f (Hole : _) []   = __IMPOSSIBLE__
	left f [] _	       = __IMPOSSIBLE__

	inside f [x]	      es      = right f x es
	inside f (Id {} : xs) es      = inside f xs es
	inside f (Hole : xs) (e : es) = do
	    e  <- toAbstractCtx InsideOperandCtx e
	    es <- inside f xs es
	    return (e : es)
	inside _ (Hole : _) [] = __IMPOSSIBLE__
	inside _ [] _	       = __IMPOSSIBLE__

	right f Hole [e] = do
	    e <- toAbstractCtx (RightOperandCtx f) e
	    return [e]
	right _ (Id {}) [] = return []
	right _ Hole    _  = __IMPOSSIBLE__
	right _ (Id {}) _  = __IMPOSSIBLE__

