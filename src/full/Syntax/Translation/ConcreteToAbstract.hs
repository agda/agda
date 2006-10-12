{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances #-}

{-| Translation from "Syntax.Concrete" to "Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Syntax.Translation.ConcreteToAbstract
    ( ToAbstract(..), BindToAbstract(..)
    , concreteToAbstract_
    , concreteToAbstract
    , OldName(..)
    ) where

import Control.Monad.Reader
import Data.Typeable

import Syntax.Concrete.Pretty ()    -- TODO: only needed for Show for the exceptions
import Syntax.Concrete as C
import Syntax.Abstract as A
import Syntax.Position
import Syntax.Common
import Syntax.Info
import Syntax.Concrete.Definitions as CD
import Syntax.Concrete.Operators
import Syntax.Fixity
import Syntax.Scope

import TypeChecking.Monad.Base (TypeError(..), Call(..), typeError)
import TypeChecking.Monad.Trace (traceCall, traceCallCPS)

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

exprSource :: C.Expr -> ScopeM ExprInfo
exprSource e = do
    par <- paren (getFixity . C.QName) e    -- TODO
    return $ ExprSource (getRange e) par

lhsArgs :: C.Pattern -> [Arg C.Pattern]
lhsArgs p = case appView p of
    Arg _ (IdentP _) : ps   -> ps
    _			    -> __IMPOSSIBLE__
    where
	mkHead	  = Arg NotHidden
	notHidden = Arg NotHidden
	appView p = case p of
	    AppP p arg	  -> appView p ++ [arg]
	    OpAppP _ x ps -> mkHead (IdentP $ C.QName x) : map notHidden ps
	    ParenP _ p	  -> appView p
	    RawAppP _ _	  -> __IMPOSSIBLE__
	    _		  -> [ mkHead p ]

{--------------------------------------------------------------------------
    Translation
 --------------------------------------------------------------------------}

concreteToAbstract_ :: ToAbstract c a => c -> ScopeM a
concreteToAbstract_ x = toAbstract x

concreteToAbstract :: ToAbstract c a => ScopeInfo -> c -> ScopeM a
concreteToAbstract i x = modScopeInfo (const i) (toAbstract x)

-- | Things that can be translated to abstract syntax are instances of this
--   class.
class ToAbstract concrete abstract | concrete -> abstract where

    toAbstract	  :: concrete -> ScopeM abstract

-- | This function should be used instead of 'toAbstract' for things that need
--   to keep track of precedences to make sure that we don't forget about it.
toAbstractCtx :: ToAbstract concrete abstract =>
		 Precedence -> concrete -> ScopeM abstract
toAbstractCtx ctx c = setContext ctx $ toAbstract c

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

instance ToAbstract NewName A.Name where
    toAbstract (NewName x) = abstractName x

instance BindToAbstract NewName A.Name where
    bindToAbstract x ret =
	do  x' <- toAbstract x
	    bindVariable x' $ ret x'

newtype OldQName = OldQName C.QName
newtype OldName = OldName C.Name

instance ToAbstract OldQName A.Expr where
    toAbstract (OldQName x) =
	do  qx <- resolveName x
	    case qx of
		VarName x'  ->
			return $
				Var (NameInfo
				    { bindingSite  = getRange x'
				    , concreteName = x
				    , nameFixity   = defaultFixity
				    , nameAccess   = PrivateAccess
				    }
				   ) (setRange (getRange x) x')
			where
			    -- TODO: move somewhere else and generalise.
			    setRange r (A.Name i (C.Name _ xs)) = A.Name i (C.Name r xs)
		DefName d   ->
		    case kindOfName d of
			FunName  -> return $ Def info $ theName d
			ConName  -> return $ Con info $ theName d
		    where
			info = NameInfo { bindingSite  = getRange d
					, concreteName = x
					, nameFixity   = fixity d
					, nameAccess   = access d
					}
		UnknownName	-> notInScope x

-- Should be a defined name.
instance ToAbstract OldName A.Name where
    toAbstract (OldName x) =
	do  qx <- resolveName (C.QName x)
	    case qx of
		DefName d   -> return $ qnameName $ theName d
		_	    -> fail $ "panic: " ++ show x ++ " should have been defined (not " ++ show qx ++ ")"

newtype CModuleName = CModuleName C.QName

instance ToAbstract CModuleName A.ModuleName where
    toAbstract (CModuleName q) = return $ A.mkModuleName q

-- | A reference to a module. Should be fully qualified when translated to
--   abstract syntax.
newtype CModuleNameRef = CModuleNameRef C.QName

instance ToAbstract CModuleNameRef A.ModuleName where
    toAbstract (CModuleNameRef q) =
	moduleName . moduleContents <$> getModule q

-- Expressions ------------------------------------------------------------

instance ToAbstract C.Expr A.Expr where

    toAbstract e = traceCall (ScopeCheckExpr e) $ case e of

    -- Names
	Ident x	-> toAbstract (OldQName x)

    -- Literals
	C.Lit l	-> return $ A.Lit l

    -- Meta variables
	C.QuestionMark r n -> do
	    scope <- getScopeInfo
	    return $ A.QuestionMark $ MetaInfo { metaRange  = r
					       , metaScope  = scope
					       , metaNumber = n
					       }
	C.Underscore r n -> do
	    scope <- getScopeInfo
	    return $ A.Underscore $ MetaInfo { metaRange  = r
					     , metaScope  = scope
					     , metaNumber = n
					     }

    -- Raw application
	C.RawApp r es -> toAbstract =<< parseApplication es

    -- Application
	C.App r e1 e2 -> do
	    e1'  <- toAbstractCtx FunctionCtx e1
	    e2'  <- toAbstract e2
	    info <- exprSource e
	    return $ A.App info e1' e2'

    -- Operator application

	C.OpApp r op es -> toAbstractOpApp r op es

    -- Malplaced hidden argument
	C.HiddenArg _ _ -> nothingAppliedToHiddenArg e

    -- Lambda
	e0@(C.Lam r bs e) ->
	    bindToAbstract bs $ \ (b:bs') -> do
		e'   <- toAbstractCtx TopCtx e
		info <- exprSource e0
		return $ A.Lam info b $ foldr mkLam e' bs'
	    where
		mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

    -- Function types
	C.Fun r e1 e2 -> do
	    let arg = case e1 of
			C.HiddenArg _ e1 -> Arg Hidden e1
			_		 -> Arg NotHidden e1
	    e1'  <- toAbstractCtx FunctionSpaceDomainCtx arg
	    e2'  <- toAbstractCtx TopCtx e2
	    info <- exprSource e
	    return $ A.Fun info e1' e2'

	e0@(C.Pi tel e) ->
	    bindToAbstract tel $ \tel -> do
		e'   <- toAbstractCtx TopCtx e
		info <- exprSource e0
		return $ A.Pi info tel e'

    -- Sorts
	C.Set _    -> flip A.Set 0 <$> exprSource e
	C.SetN _ n -> flip A.Set n <$> exprSource e
	C.Prop _   -> A.Prop <$> exprSource e

    -- Let
	e0@(C.Let _ ds e) ->
	    bindToAbstract (LetDefs ds) $ \ds' -> do
		e'   <- toAbstractCtx TopCtx e
		info <- exprSource e0
		return $ A.Let info ds' e'

    -- Parenthesis
	C.Paren _ e -> toAbstractCtx TopCtx e
	-- You could imagine remembering parenthesis. I don't really see the
	-- point though.

    -- Pattern things
	C.As _ _ _ -> notAnExpression e
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
    bindToAbstract (C.TBind r xs t) ret =
	do  t' <- toAbstractCtx TopCtx t
	    bindToAbstract (map NewName xs) $ \xs' ->
		ret (A.TBind r xs' t')
    bindToAbstract (C.TNoBind e) ret =
	do  e <- toAbstractCtx TopCtx e
	    ret (A.TNoBind e)

-- Note: only for top level modules!
instance ToAbstract C.Declaration (A.Declaration, ScopeInfo) where
    toAbstract (C.Module r x tel ds) =
	insideTopLevelModule x $
	bindToAbstract (tel,ds) $ \(tel',ds') ->    -- order matter!
	    do	scope <- getScopeInfo
		x' <- toAbstract $ CModuleName x
		return (A.Module info x' tel' ds', scope)
	where
	    info = mkRangedModuleInfo PublicAccess r
			-- We could save the concrete module here but
			-- seems a bit over-kill.
    toAbstract d = __IMPOSSIBLE__

instance BindToAbstract [C.Declaration] [A.Declaration] where
    bindToAbstract ds =
	bindToAbstract (niceDeclarations ds)

instance BindToAbstract [NiceDeclaration] [A.Declaration] where
    bindToAbstract [] ret = ret []
    bindToAbstract (x:xs) ret =
	bindToAbstract (x,xs) $ \ (y,ys) -> ret (y ++ ys)

newtype LetDefs = LetDefs [C.Declaration]
newtype LetDef = LetDef NiceDeclaration

instance BindToAbstract LetDefs [A.LetBinding] where
    bindToAbstract (LetDefs ds) = bindToAbstract (map LetDef $ niceDeclarations ds)

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

	    lambda e (Arg h (A.VarP x)) = return $ A.Lam i (A.DomainFree h x) e
		where
		    i = ExprRange (fuseRange x e)
	    lambda e (Arg h (A.WildP i)) =
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
instance BindToAbstract NiceDefinition Definition where

    -- Function definitions
    bindToAbstract (CD.FunDef r ds f p a x cs) ret =
	do  (x',cs') <- toAbstract (OldName x,cs)
	    ret $ A.FunDef (mkSourcedDefInfo x f p a ds) x' cs'

    -- Data definitions
    bindToAbstract (CD.DataDef r f p a x pars cons) ret = do
	(pars,cons) <- bindToAbstract pars $ \pars ->
		       bindToAbstract (map Constr cons) $ \cons ->
		       return (pars,cons)
	x' <- toAbstract (OldName x)
	bindToAbstract (map Constr cons) $ \_ ->
	    ret $ A.DataDef (mkRangedDefInfo x f p a r) x' pars cons

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list. Except we keep open
-- declarations. Oh well...
instance BindToAbstract NiceDeclaration [A.Declaration] where

    bindToAbstract d ret = 
	traceCallCPS (ScopeCheckDeclaration d) ret $ \ret -> case d of

    -- Axiom
	CD.Axiom r f p a x t -> do
	    t' <- toAbstractCtx TopCtx t
	    defineName p FunName f x $ \x' -> do
		ret [A.Axiom (mkRangedDefInfo x f p a r) x' t']
				-- we can easily reconstruct the original decl
				-- so we don't bother save it

    -- Primitive function
	PrimitiveFunction r f p a x t -> do
	    t' <- toAbstractCtx TopCtx t
	    defineName p FunName f x $ \x' ->
		ret [A.Primitive (mkRangedDefInfo x f p a r) x' t']
				-- we can easily reconstruct the original decl
				-- so we don't bother save it

    -- Definitions (possibly mutual)
	NiceDef r cs ts ds ->
	    bindToAbstract (ts,ds) $ \ (ts',ds') ->
		ret [Definition (DeclInfo C.noName_ $ DeclSource cs) ts' ds']
		    -- TODO: remember name


    -- TODO: what does an abstract module mean? The syntax doesn't allow it.
	NiceModule r p _ name@(C.QName x) tel ds -> do
	    (tel',ds',ns) <-
		insideModule x $
		bindToAbstract (tel,ds) $ \ (tel',ds') ->
		    do	ns <- currentNameSpace
			return (tel',ds',ns)
	    let m = ModuleScope { moduleArity	 = length tel
			        , moduleAccess	 = p
			        , moduleContents = ns
			        }
	    name' <- toAbstract $ CModuleName name
	    defineModule x m $
		ret [A.Module (mkRangedModuleInfo p r)
			      name' tel' ds']

    -- Top-level modules are translated with toAbstract.
	NiceModule _ _ _ _ _ _ -> __IMPOSSIBLE__

	NiceModuleMacro r p _ x tel e is -> case appView e of
	    AppView (Ident m) args  ->
		bindToAbstract tel $ \tel' ->
		    do	(x',m',args') <- toAbstract ( CModuleName $ C.QName x
						    , CModuleNameRef m
						    , args
						    )
			implicitModule x p (length tel) m is $
			    ret [ ModuleDef (mkSourcedModuleInfo p
						[C.ModuleMacro r x tel e is]
					    )
					    x' tel' m' args'
				]
		    
	    _	-> notAModuleExpr e

	NiceOpen r x is ->
	    openModule x is $ ret [A.Open $ DeclSource [C.Open r x is]]

	NicePragma r p -> do
	    p <- toAbstract p
	    ret [A.Pragma r p]

	NiceImport r x as is -> do
	    x' <- toAbstract $ CModuleName x
	    i  <- scopeCheckImport x'
	    importModule name i is $
		ret [A.Import (mkSourcedModuleInfo PublicAccess [C.Import r x as is]) x']
	    where
		name = maybe x C.QName as

newtype Constr a = Constr a

instance BindToAbstract (Constr CD.NiceDeclaration) A.Declaration where
    bindToAbstract (Constr (CD.Axiom r f p a x t)) ret = do
	t' <- toAbstractCtx TopCtx t
	defineName p' ConName f x $ \x' ->
	    ret (A.Axiom (mkRangedDefInfo x f p a r) x' t')
	where
	    -- An abstract constructor is private (abstract constructor means
	    -- abstract datatype, so the constructor should not be exported).
	    p' = case (a, p) of
		    (AbstractDef, _) -> PrivateAccess
		    (_, p)	     -> p

    bindToAbstract _ _ = __IMPOSSIBLE__    -- a constructor is always an axiom

instance BindToAbstract (Constr A.Declaration) () where
    bindToAbstract (Constr (A.Axiom info x _)) ret =
	    modScopeInfoM (defName p ConName fx x) $ ret ()
	where
	    a  = defAccess info
	    fx = defFixity info
	    p  = case (defAbstract info, defAccess info) of
		    (AbstractDef, _) -> PrivateAccess
		    (_, p)	     -> p
    bindToAbstract _ _ = __IMPOSSIBLE__ -- a constructor is always an axiom

instance ToAbstract CD.Clause A.Clause where
    toAbstract (CD.Clause top lhs rhs wh) =
	bindToAbstract (LeftHandSide top lhs) $ \lhs' ->	-- the order matters here!
	bindToAbstract wh  $ \wh'  ->
	    do	rhs' <- toAbstractCtx TopCtx rhs
		return $ A.Clause lhs' rhs' wh'

data LeftHandSide = LeftHandSide C.Name C.LHS

instance BindToAbstract LeftHandSide A.LHS where
    bindToAbstract (LeftHandSide top lhs) ret =
	traceCallCPS (ScopeCheckLHS top lhs) ret $ \ret -> do
	p <- parseLHS top lhs
	bindToAbstract (lhsArgs p) $ \args -> do
	    x <- toAbstract (OldName top)
	    ret (A.LHS (LHSSource lhs) x args)

instance BindToAbstract c a => BindToAbstract (Arg c) (Arg a) where
    bindToAbstract (Arg h e) ret = bindToAbstract e $ ret . Arg h

instance ToAbstract c a => ToAbstract (Arg c) (Arg a) where
    toAbstract (Arg h e) = Arg h <$> toAbstractCtx (hiddenArgumentCtx h) e

instance BindToAbstract C.Pattern A.Pattern where
    bindToAbstract p@(C.IdentP x) ret =
	do  rx <- resolvePatternNameM x
	    case rx of
		VarName y   -> bindVariable y $ ret $ VarP y
		DefName d
		    | kindOfName d == ConName -> do
			let y = theName d
			ret $ ConP (PatSource (getRange p) $ const p) y []
		    | kindOfName d == FunName -> do
			let y = theName d
			ret $ DefP (PatSource (getRange p) $ const p) y []
		UnknownName -> notInScope x
		_	    -> __IMPOSSIBLE__
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
		ConP _ x as -> ret $ ConP info x (as ++ map (Arg NotHidden) ps)
		DefP _ x as -> ret $ DefP info x (as ++ map (Arg NotHidden) ps)
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
    bindToAbstract p0@(C.AbsurdP r) ret = ret (A.AbsurdP info)
	where
	    info = PatSource r $ \_ -> p0

-- Helpers for OpApp case

  -- let's deal with the binary case (there should be no special casing
  -- in future.)
toAbstractOpApp r op@(C.Name _ [Hole, Id _, Hole]) es@[e1, e2] = do
        let e = C.OpApp r op es
	x    <- toAbstract (OldQName $ C.QName op)
    	f    <- getFixity (C.QName op)
	e1'  <- toAbstractCtx (LeftOperandCtx  f) e1
	e2'  <- toAbstractCtx (RightOperandCtx f) e2
	info <- exprSource e
	return $ foldl app x [e1', e2']
	where
	    app e arg = A.App (ExprRange (fuseRange e arg)) e
		      $ Arg NotHidden arg

  -- other cases are not seriously considered, but should be safe.
toAbstractOpApp r op es = do
        let e = C.OpApp r op es
	x    <- toAbstract (OldQName $ C.QName op)
	es'  <- toAbstractCtx ArgumentCtx es -- the safe verbose way
	info <- exprSource e
	return $ foldl app x es'
	where
	    app e arg = A.App (ExprRange (fuseRange e arg)) e
		      $ Arg NotHidden arg
