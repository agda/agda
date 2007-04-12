{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances #-}

{-| Translation from "Syntax.Concrete" to "Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Syntax.Translation.ConcreteToAbstract
    ( ToAbstract(..), BindToAbstract(..)
    , concreteToAbstract_
    , concreteToAbstract
    , OldName(..)
    , TopLevel(..)
    ) where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Data.Typeable
import Data.Traversable (mapM)

import Syntax.Concrete as C
import Syntax.Abstract as A
import Syntax.Position
import Syntax.Common
import Syntax.Info
import Syntax.Concrete.Definitions as CD
import Syntax.Concrete.Operators
import Syntax.Fixity
import Syntax.Scope.Base
import Syntax.Scope.Monad
import Syntax.Strict

import TypeChecking.Monad.Base (TypeError(..), Call(..), typeError)
import TypeChecking.Monad.Trace (traceCall, traceCallCPS)
import TypeChecking.Monad.State (withScope_, getScope)

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

{--------------------------------------------------------------------------
    Helpers
 --------------------------------------------------------------------------}

lhsArgs :: C.Pattern -> [NamedArg C.Pattern]
lhsArgs p = case appView p of
    Arg _ (Named _ (IdentP _)) : ps -> ps
    _				    -> __IMPOSSIBLE__
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
makeSection _    _ []  ds = ds
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

bindToAbstractCtx :: BindToAbstract concrete abstract =>
		     Precedence -> concrete -> (abstract -> ScopeM a) -> ScopeM a
bindToAbstractCtx ctx c ret = setContextCPS ctx ret (bindToAbstract c)

-- | Things that can be translated to abstract syntax and in the process
--   update the scope are instances of this class.
class BindToAbstract concrete abstract | concrete -> abstract where
    bindToAbstract :: concrete -> (abstract -> ScopeM a) -> ScopeM a

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

instance (BindToAbstract c1 a1, BindToAbstract c2 a2) => BindToAbstract (c1,c2) (a1,a2) where
    bindToAbstract (x,y) ret =
	bindToAbstract x $ \x' ->
	bindToAbstract y $ \y' ->
	ret (x',y')

instance BindToAbstract c a => BindToAbstract [c] [a] where
    bindToAbstract [] ret = ret []
    bindToAbstract (x:xs) ret =
	bindToAbstract (x,xs) $ \ (y,ys) -> ret (y:ys)

-- Names ------------------------------------------------------------------

newtype NewName = NewName C.Name
newtype OldQName = OldQName C.QName
newtype OldName = OldName C.Name
newtype PatName = PatName C.QName

instance ToAbstract NewName A.Name where
  toAbstract (NewName x) = freshAbstractName x

instance BindToAbstract NewName A.Name where
  bindToAbstract x@(NewName x') ret = do
    y <- toAbstract x
    bindVariable x' y $ ret y

varInfo :: NameInfo
varInfo = NameInfo { nameFixity = defaultFixity
		   , nameAccess = PrivateAccess
		   }

nameExpr :: AbstractName -> A.Expr
nameExpr d = mk (anameKind d) info $ anameName d
  where
    mk DefName = Def
    mk ConName = Con

    info = NameInfo { nameFixity = anameFixity d
		    , nameAccess = __IMPOSSIBLE__ -- TODO
		    }

instance ToAbstract OldQName A.Expr where
  toAbstract (OldQName x) = do
    qx <- resolveName x
    case qx of
      VarName x'    -> return $ A.Var varInfo x'
      DefinedName d -> return $ nameExpr d
      UnknownName   -> notInScope x

data APatName = VarPatName A.Name
	      | ConPatName AbstractName

instance BindToAbstract PatName APatName where
  bindToAbstract (PatName x) ret = do
    rx <- resolveName x
    z  <- case (rx, x) of
      -- TODO: warn about shadowing
      (VarName y,	C.QName x)			  -> return $ Left x
      (DefinedName d, C.QName x) | DefName == anameKind d -> return $ Left x
      (UnknownName,	C.QName x)			  -> return $ Left x
      (DefinedName d, _	 )	 | ConName == anameKind d -> return $ Right d
      _							  -> fail $ "not a constructor: " ++ show x -- TODO
    case z of
      Left x  -> bindToAbstract (NewName x) $ ret . VarPatName
      Right c -> ret (ConPatName c)

-- Should be a defined name.
instance ToAbstract OldName A.QName where
  toAbstract (OldName x) = do
    rx <- resolveName (C.QName x)
    case rx of
      DefinedName d -> return $ anameName d
      _		    -> __IMPOSSIBLE__
	  -- fail $ "panic: " ++ show x ++ " should have been defined (not " ++ show rx ++ ")"

newtype NewModuleName  = NewModuleName  C.Name
newtype NewModuleQName = NewModuleQName C.QName
newtype OldModuleName  = OldModuleName  C.QName

instance ToAbstract NewModuleName A.Name where
  toAbstract (NewModuleName x) = freshAbstractName x

instance ToAbstract NewModuleQName A.ModuleName where
  toAbstract (NewModuleQName q) =
    qnameFromList <$> mapM (toAbstract . NewModuleName) (toList q)
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

  -- Malplaced hidden argument
      C.HiddenArg _ _ -> nothingAppliedToHiddenArg e

  -- Lambda
      e0@(C.Lam r bs e) -> do
	bindToAbstract bs $ \(b:bs') -> do
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
	bindToAbstract tel $ \tel -> do
	e    <- toAbstractCtx TopCtx e
	let info = ExprRange (getRange e0)
	return $ A.Pi info tel e

  -- Sorts
      C.Set _    -> return $ A.Set (ExprRange $ getRange e) 0
      C.SetN _ n -> return $ A.Set (ExprRange $ getRange e) n
      C.Prop _   -> return $ A.Prop $ ExprRange $ getRange e

  -- Let
      e0@(C.Let _ ds e) ->
	bindToAbstract (LetDefs ds) $ \ds' -> do
	e	 <- toAbstractCtx TopCtx e
	let info = ExprRange (getRange e0)
	return $ A.Let info ds' e

  -- Parenthesis
      C.Paren _ e -> toAbstractCtx TopCtx e

  -- Pattern things
      C.As _ _ _ -> notAnExpression e
      C.Dot _ _  -> notAnExpression e
      C.Absurd _ -> notAnExpression e

instance BindToAbstract C.LamBinding A.LamBinding where
  bindToAbstract (C.DomainFree h x) ret =
    bindToAbstract (NewName x) $ \x' ->
      ret (A.DomainFree h x')
  bindToAbstract (C.DomainFull tb) ret =
    bindToAbstract tb $ \tb' -> ret (A.DomainFull tb')

instance BindToAbstract C.TypedBindings A.TypedBindings where
  bindToAbstract (C.TypedBindings r h bs) ret =
    bindToAbstract bs $ \bs ->
    ret (A.TypedBindings r h bs)

instance BindToAbstract C.TypedBinding A.TypedBinding where
  bindToAbstract (C.TBind r xs t) ret = do
    t' <- toAbstractCtx TopCtx t
    bindToAbstract (map NewName xs) $ \xs' ->
      ret (A.TBind r xs' t')
  bindToAbstract (C.TNoBind e) ret = do
    e <- toAbstractCtx TopCtx e
    ret (A.TNoBind e)

newtype TopLevel a = TopLevel a

scopeCheckModule :: Range -> Access -> IsAbstract -> C.Name -> C.Telescope -> [C.Declaration] ->
		    ScopeM [A.Declaration]
scopeCheckModule r a c x tel ds = do
  m <- toAbstract (NewModuleName x)
  pushScope m
  qm <- getCurrentModule
  ds <- bindToAbstract tel $ \tel ->
	  makeSection info qm tel <$> toAbstract ds
  popScope
  bindModule a (length tel) x qm
  return ds
  where
    info = mkRangedModuleInfo a c r

-- Top-level declarations are always (import|open)* module
instance ToAbstract (TopLevel [C.Declaration]) ([A.Declaration], ScopeInfo) where
    toAbstract (TopLevel ds) = case splitAt (length ds - 1) ds of
	(ds', [C.Module r (C.Qual m x) tel ds]) ->
	  toAbstract $ TopLevel $ ds' ++
	    [ C.Module r (C.QName m) [] 
	      [ C.Module r x tel ds ]
	    ]
	(ds', [C.Module r (C.QName x) tel ds]) -> do
	    ds' <- toAbstract ds'
	    ds  <- scopeCheckModule r PublicAccess ConcreteDef x tel ds
	    scope <- getScope
	    return (ds' ++ ds, scope)
	    where
	_ -> __IMPOSSIBLE__

instance ToAbstract [C.Declaration] [A.Declaration] where
  toAbstract = toAbstract . niceDeclarations

newtype LetDefs = LetDefs [C.Declaration]
newtype LetDef = LetDef NiceDeclaration

instance BindToAbstract LetDefs [A.LetBinding] where
    bindToAbstract (LetDefs ds) ret =
	bindToAbstract (map LetDef $ niceDeclarations ds) ret

instance ToAbstract C.RHS A.RHS where
    toAbstract C.AbsurdRHS = return $ A.AbsurdRHS
    toAbstract (C.RHS e)   = A.RHS <$> toAbstract e

instance BindToAbstract LetDef A.LetBinding where
    bindToAbstract (LetDef d) ret =
	case d of
	    NiceDef _ c [CD.Axiom _ _ _ _ x t] [CD.FunDef _ _ _ _ _ _ [cl]] ->
		do  e <- letToAbstract cl
		    t <- toAbstract t
		    bindToAbstract (NewName x) $ \x ->
			ret (A.LetBind (LetSource c) x t e)
	    _	-> notAValidLetBinding d
	where
	    letToAbstract (CD.Clause top clhs (C.RHS rhs) []) = do
		p    <- parseLHS top clhs
		bindToAbstract (lhsArgs p) $ \args ->
		    do	rhs <- toAbstract rhs
			foldM lambda rhs args
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

instance ToAbstract C.Pragma A.Pragma where
    toAbstract (C.OptionsPragma _ opts) = return $ A.OptionsPragma opts
    toAbstract (C.BuiltinPragma _ b e) = do
	e <- toAbstract e
	return $ A.BuiltinPragma b e

-- Only constructor names are bound by definitions.
instance ToAbstract NiceDefinition Definition where

    -- Function definitions
    toAbstract (CD.FunDef r ds f p a x cs) =
	do  (x',cs') <- toAbstract (OldName x,cs)
	    return $ A.FunDef (mkSourcedDefInfo x f p a ds) x' cs'

    -- Data definitions
    toAbstract (CD.DataDef r f p a x pars cons) = do
	(pars,cons) <- bindToAbstract pars $ \pars -> do
			cons <- toAbstract (map Constr cons)
			return (pars, cons)
	x' <- toAbstract (OldName x)
	-- toAbstract (map Constr cons) TODO!!
	return $ A.DataDef (mkRangedDefInfo x f p a r) x' pars cons

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list.
instance ToAbstract NiceDeclaration A.Declaration where

  toAbstract d = annotateDecls =<< case d of  -- TODO: trace call

  -- Axiom
    CD.Axiom r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      x' <- bindName p DefName f x
      return [ A.Axiom (mkRangedDefInfo x f p a r) x' t' ]

  -- Primitive function
    PrimitiveFunction r f p a x t -> do
      t' <- toAbstractCtx TopCtx t
      x' <- bindName p DefName f x
      return [ A.Primitive (mkRangedDefInfo x f p a r) x' t' ]

  -- Definitions (possibly mutual)
    NiceDef r cs ts ds -> do
      (ts', ds') <- toAbstract (ts, ds)
      return [ Definition (DeclInfo C.noName_ $ DeclRange r) ts' ds' ]
			  -- TODO: what does the info mean here?

  -- TODO: what does an abstract module mean? The syntax doesn't allow it.
    NiceModule r p a name@(C.QName x) tel ds -> scopeCheckModule r p a x tel ds

  -- Top-level modules are translated with toAbstract.
    NiceModule _ _ _ _ _ _ -> __IMPOSSIBLE__

    NiceModuleMacro r p a x tel e open dir -> case appView e of
      AppView (Ident m) args  ->
	bindToAbstract tel $ \tel' -> do
	  (x',m1,args') <- toAbstract ( NewModuleName x
				      , OldModuleName m
				      , args
				      )
	  pushScope x'
	  m0 <- getCurrentModule
	  openModule_ m $ dir { C.publicOpen = True }
	  modifyTopScope $ freshCanonicalNames m1 m0
	  popScope
	  bindModule p (length tel) x m0
	  case open of
	    DontOpen -> return ()
	    DoOpen   -> openModule_ (C.QName x) dir
	  let decl = Apply info m0 m1 args'
	  case tel' of
	    []  -> return [ decl ]
	    _	  -> do
	      -- If the module is reabstracted we create an anonymous
	      -- section around it.
	      noName <- freshAbstractName $ C.noName $ getRange x
	      top    <- getCurrentModule
	      return $ makeSection info (A.qualify top noName) tel' [ decl ]
      _	-> notAModuleExpr e
      where
	info = mkRangedModuleInfo p a r

    NiceOpen r x dir -> do
      current <- getCurrentModule
      m	      <- toAbstract (OldModuleName x)
      n	      <- length . scopeLocals <$> getScope

      -- Opening a submodule or opening into a non-parameterised module
      -- is fine. Otherwise we have to create a temporary module.
      if m `isSubModuleOf` current || n == 0
	then do
	  openModule_ x dir
	  return []
	else do
	  let tmp = C.noName (getRange x) -- TODO: better name?
	  d <- toAbstract $ NiceModuleMacro r PrivateAccess ConcreteDef
					    tmp [] (C.Ident x) DoOpen dir
	  return [d]

    NicePragma r p -> do
      p <- toAbstract p
      return [ A.Pragma r p ]

    NiceImport r x as open dir -> do
      m	  <- toAbstract $ NewModuleQName x
      i	  <- applyImportDirective dir <$> scopeCheckImport m
      modifyTopScope (`mergeScope` i)
      bindQModule PrivateAccess (error "TODO __FILE__:__LINE__: unknown arity") -- TODO!!
		  name m
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

instance ToAbstract (Constr CD.NiceDeclaration) A.Declaration where
    toAbstract (Constr (CD.Axiom r f p a x t)) = do
	t' <- toAbstractCtx TopCtx t
	x' <- bindName p' ConName f x
	return $ A.Axiom (mkRangedDefInfo x f p a r) x' t'
	where
	    -- An abstract constructor is private (abstract constructor means
	    -- abstract datatype, so the constructor should not be exported).
	    p' = case (a, p) of
		    (AbstractDef, _) -> PrivateAccess
		    (_, p)	     -> p

    toAbstract _ = __IMPOSSIBLE__    -- a constructor is always an axiom

-- TODO!!
-- instance ToAbstract (Constr A.Declaration) () where
--   toAbstract (Constr (A.Axiom info x _)) = undefined -- TODO!!
-- -- 	    modScopeInfoM (defName p ConName fx x) $ ret ()
-- -- 	where
-- -- 	    a  = defAccess info
-- -- 	    fx = defFixity info
-- -- 	    p  = case (defAbstract info, defAccess info) of
-- -- 		    (AbstractDef, _) -> PrivateAccess
-- -- 		    (_, p)	     -> p
--   toAbstract _ = __IMPOSSIBLE__ -- a constructor is always an axiom

instance ToAbstract CD.Clause A.Clause where
    toAbstract (CD.Clause top lhs rhs wh) =
	bindToAbstract (LeftHandSide top lhs) $ \lhs' -> do	-- the order matters here!
	  wh'  <- toAbstract wh	-- TODO!! ?
	  rhs' <- toAbstractCtx TopCtx rhs
	  return $ A.Clause lhs' rhs' wh'

data LeftHandSide = LeftHandSide C.Name C.LHS

instance BindToAbstract LeftHandSide A.LHS where
    bindToAbstract (LeftHandSide top lhs) ret =
	traceCallCPS (ScopeCheckLHS top lhs) ret $ \ret -> do
	p <- parseLHS top lhs
	bindToAbstract (lhsArgs p) $ \args -> do
	    args <- toAbstract args -- take care of dot patterns
	    x	 <- toAbstract (OldName top)
	    ret (A.LHS (LHSSource lhs) x args)

instance BindToAbstract c a => BindToAbstract (Arg c) (Arg a) where
    bindToAbstract (Arg h e) ret = bindToAbstractCtx (hiddenArgumentCtx h) e $ ret . Arg h

instance BindToAbstract c a => BindToAbstract (Named name c) (Named name a) where
    bindToAbstract (Named n e) ret = bindToAbstract e $ ret . Named n

instance ToAbstract c a => ToAbstract (Arg c) (Arg a) where
    toAbstract (Arg h e) = Arg h <$> toAbstractCtx (hiddenArgumentCtx h) e

instance ToAbstract c a => ToAbstract (Named name c) (Named name a) where
    toAbstract (Named n e) = Named n <$> toAbstract e

-- Patterns are done in two phases. First everything but the dot patterns, and
-- then the dot patterns. This is because dot patterns can refer to variables
-- bound anywhere in the pattern.

instance ToAbstract c a => ToAbstract (A.Pattern' c) (A.Pattern' a) where
    toAbstract = mapM toAbstract

instance BindToAbstract C.Pattern (A.Pattern' C.Expr) where

    bindToAbstract p@(C.IdentP x) ret =
	bindToAbstract (PatName x) $ \px ->
	case px of
	    VarPatName y -> ret $ VarP y
	    ConPatName d -> ret $ ConP (PatRange (getRange p)) (anameName d) []

    bindToAbstract p0@(AppP p q) ret =
	bindToAbstract (p,q) $ \(p',q') ->
	case p' of
	    ConP _ x as -> ret $ ConP info x (as ++ [q'])
	    DefP _ x as -> ret $ DefP info x (as ++ [q'])
	    _		-> __IMPOSSIBLE__
	where
	    r = getRange p0
	    info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    bindToAbstract p0@(OpAppP r op ps) ret =
	bindToAbstract (IdentP $ C.QName op)
			  $ \p ->
	bindToAbstract ps $ \ps ->
	    case p of
		ConP _ x as -> ret $ ConP info x (as ++ map (Arg NotHidden . unnamed) ps)
		DefP _ x as -> ret $ DefP info x (as ++ map (Arg NotHidden . unnamed) ps)
		_	    -> __IMPOSSIBLE__
	where
	    r = getRange p0
	    info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    -- Removed when parsing
    bindToAbstract (HiddenP _ _) _ = __IMPOSSIBLE__
    bindToAbstract (RawAppP _ _) _ = __IMPOSSIBLE__

    bindToAbstract p@(C.WildP r)    ret = ret $ A.WildP (PatSource r $ const p)
    bindToAbstract (C.ParenP _ p)   ret = bindToAbstract p ret
    bindToAbstract (C.LitP l)	    ret = ret $ A.LitP l
    bindToAbstract p0@(C.AsP r x p) ret =
	bindToAbstract (NewName x) $ \x ->
	bindToAbstract p $ \p ->
	    ret (A.AsP info x p)
	where
	    info = PatSource r $ \_ -> p0
    -- we have to do dot patterns at the end
    bindToAbstract p0@(C.DotP r e) ret = ret $ A.DotP info e
	where info = PatSource r $ \_ -> p0
    bindToAbstract p0@(C.AbsurdP r) ret = ret (A.AbsurdP info)
	where
	    info = PatSource r $ \_ -> p0

-- | Turn an operator application into abstract syntax. Make sure to record the
-- right precedences for the various arguments.
toAbstractOpApp :: Range -> C.Name -> [C.Expr] -> ScopeM A.Expr
toAbstractOpApp r op@(C.Name _ xs) es = do
    f  <- getFixity (C.QName op)
    op <- toAbstract (OldQName $ C.QName op) -- op-apps cannot bind the op
    foldl app op <$> left f xs es
    where
	app e arg = A.App (ExprRange (fuseRange e arg)) e
		  $ Arg NotHidden $ unnamed arg

	left f (Hole : xs) (e : es) = do
	    e  <- toAbstractCtx (LeftOperandCtx f) e
	    es <- inside f xs es
	    return (e : es)
	left f (Id _ : xs) es = inside f xs es
	left f (Hole : _) []  = __IMPOSSIBLE__
	left f [] _	      = __IMPOSSIBLE__

	inside f [x]	      es      = right f x es
	inside f (Id _ : xs)  es      = inside f xs es
	inside f (Hole : xs) (e : es) = do
	    e  <- toAbstractCtx InsideOperandCtx e
	    es <- inside f xs es
	    return (e : es)
	inside _ (Hole : _) [] = __IMPOSSIBLE__
	inside _ [] _	       = __IMPOSSIBLE__

	right f Hole [e] = do
	    e <- toAbstractCtx (RightOperandCtx f) e
	    return [e]
	right _ (Id _) [] = return []
	right _ Hole _	  = __IMPOSSIBLE__
	right _ (Id _) _  = __IMPOSSIBLE__

