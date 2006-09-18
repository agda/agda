{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances #-}

{-| Translation from "Syntax.Concrete" to "Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Syntax.Translation.ConcreteToAbstract
    ( ToAbstract(..), BindToAbstract(..)
    , concreteToAbstract_
    , concreteToAbstract
    , ToAbstractException(..)
    ) where

import Control.Exception
import Control.Monad.Reader
import Data.Typeable

import Syntax.Concrete.Pretty ()    -- TODO: only needed for Show for the exceptions
import Syntax.Concrete as C
import Syntax.Abstract as A
import Syntax.Position
import Syntax.Common
import Syntax.Info
--import Syntax.Interface
import Syntax.Concrete.Definitions as CD
import Syntax.Concrete.Operators
import Syntax.Fixity
import Syntax.Scope

import Interaction.Imports

import Utils.Monad
import Utils.Tuple

#include "../../undefined.h"


{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

data ToAbstractException
	= HigherOrderPattern C.Pattern C.Pattern
	    -- ^ the first pattern is an application and the second
	    --	 pattern is the function part (and it's not
	    --	 a constructor pattern).
	| NotAModuleExpr C.Expr
	    -- ^ The expr was used in the right hand side of an implicit module
	    --	 definition, but it wasn't of the form @m Delta@.
	| NoTopLevelModule C.Declaration
	| NotAnExpression C.Expr
	| NotAValidLetBinding NiceDeclaration
	| NotAValidLHS C.Pattern
	| NothingAppliedToHiddenArg C.Expr
	| NothingAppliedToHiddenPat C.Pattern
    deriving (Typeable, Show)

higherOrderPattern p0 p	    = throwDyn $ HigherOrderPattern p0 p
notAModuleExpr e	    = throwDyn $ NotAModuleExpr e
noTopLevelModule d	    = throwDyn $ NoTopLevelModule d
notAnExpression e	    = throwDyn $ NotAnExpression e
notAValidLetBinding d	    = throwDyn $ NotAValidLetBinding d
notAValidLHS p		    = throwDyn $ NotAValidLHS p
nothingAppliedToHiddenArg e = throwDyn $ NothingAppliedToHiddenArg e
nothingAppliedToHiddenPat e = throwDyn $ NothingAppliedToHiddenPat e

instance HasRange ToAbstractException where
    getRange (HigherOrderPattern p _)	   = getRange p
    getRange (NotAModuleExpr e)		   = getRange e
    getRange (NoTopLevelModule d)	   = getRange d
    getRange (NotAnExpression e)	   = getRange e
    getRange (NotAValidLetBinding d)	   = getRange d
    getRange (NotAValidLHS p)		   = getRange p
    getRange (NothingAppliedToHiddenArg e) = getRange e
    getRange (NothingAppliedToHiddenPat e) = getRange e

{--------------------------------------------------------------------------
    Helpers
 --------------------------------------------------------------------------}

exprSource :: C.Expr -> ScopeM ExprInfo
exprSource e =
    do	f <- getFixityFunction
	let f' x = f (C.QName x)    -- TODO
	return $ ExprSource (getRange e) (paren f' e)

lhsArgs :: C.Pattern -> ScopeM [Arg C.Pattern]
lhsArgs p = case appView p of
    Arg _ (IdentP _) : ps   -> return ps
    _			    -> notAValidLHS p
    where
	mkHead	  = Arg NotHidden
	notHidden = Arg NotHidden
	appView p = case p of
	    AppP p arg	  -> appView p ++ [arg]
	    OpAppP _ x ps -> mkHead (IdentP $ C.QName $ nameDeclName x) : map notHidden ps
	    RawAppP _ _	  -> __IMPOSSIBLE__
	    _		  -> [ mkHead p ]

{--------------------------------------------------------------------------
    Translation
 --------------------------------------------------------------------------}

concreteToAbstract_ :: ToAbstract c a => c -> IO a
concreteToAbstract_ x = runScopeM_ (toAbstract x)

concreteToAbstract :: ToAbstract c a => ScopeState -> ScopeInfo -> c -> IO a
concreteToAbstract s i x = runScopeM s i (toAbstract x)

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
	do  qx <- resolveNameM x
	    case qx of
		VarName x'  ->
			return $
				Var (NameInfo
				    { bindingSite  = getRange x'
				    , concreteName = x
				    , nameOperator = defaultOperator $ nameConcrete x'
				    , nameAccess   = PrivateAccess
				    }
				   ) (setRange (getRange x) x')
			where
			    -- TODO: move somewhere else and generalise.
			    setRange r (A.Name i (C.Name _ x)) = A.Name i (C.Name r x)
			    setRange r (A.Name i (C.NoName _)) = A.Name i (C.NoName r)
		DefName d   ->
		    case kindOfName d of
			FunName  -> return $ Def info $ theName d
			ConName  -> return $ Con info $ theName d
		    where
			info = NameInfo { bindingSite   = getRange d
					, concreteName  = x
					, nameOperator	= operator d
					, nameAccess    = access d
					}
		UnknownName	-> notInScope x

-- Should be a defined name.
instance ToAbstract OldName A.Name where
    toAbstract (OldName x) =
	do  qx <- resolveNameM (C.QName x)
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

    -- Names
    toAbstract (Ident x) = toAbstract (OldQName x)

    -- Literals
    toAbstract (C.Lit l)     = return $ A.Lit l
    toAbstract e@(C.List r es) = do
	es   <- toAbstractCtx TopCtx es
	info <- exprSource e
	return $ A.List info es

    -- Meta variables
    toAbstract (C.QuestionMark r n) =
	do  scope <- getScopeInfo
	    return $ A.QuestionMark $ MetaInfo { metaRange  = r
					       , metaScope  = scope
					       , metaNumber = n
					       }
    toAbstract (C.Underscore r n) =
	do  scope <- getScopeInfo
	    return $ A.Underscore $ MetaInfo { metaRange  = r
					     , metaScope  = scope
					     , metaNumber = n
					     }

    -- Raw application
    toAbstract e@(C.RawApp r es) = toAbstract =<< parseApplication es

    -- Application
    toAbstract e@(C.App r e1 e2) =
	do  e1'  <- toAbstractCtx FunctionCtx e1
	    e2'  <- toAbstract e2
	    info <- exprSource e
	    return $ A.App info e1' e2'

    -- Operator application
    toAbstract e@(C.OpApp r op es) = do
	x    <- toAbstract (OldQName $ C.QName $ nameDeclName op)
	es'  <- toAbstract es	-- TODO: parenthesis?
	info <- exprSource e
	return $ foldl app x es'
	where
	    app e arg = A.App (ExprRange (fuseRange e arg)) e
		      $ Arg NotHidden arg

    -- Malplaced hidden argument
    toAbstract e@(C.HiddenArg _ _) = nothingAppliedToHiddenArg e

    -- Lambda
    toAbstract e0@(C.Lam r bs e) =
	bindToAbstract bs $ \ (b:bs') ->
	    do  e'   <- toAbstractCtx TopCtx e
		info <- exprSource e0
		return $ A.Lam info b $ foldr mkLam e' bs'
	where
	    mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

    -- Function types
    toAbstract e@(C.Fun r e1 e2) =
	do  let arg = case e1 of
			C.HiddenArg _ e1 -> Arg Hidden e1
			_		 -> Arg NotHidden e1
	    e1'  <- toAbstractCtx FunctionSpaceDomainCtx arg
	    e2'  <- toAbstractCtx TopCtx e2
	    info <- exprSource e
	    return $ A.Fun info e1' e2'

    toAbstract e0@(C.Pi tel e) =
	bindToAbstract tel $ \tel ->
	do  e'	 <- toAbstractCtx TopCtx e
	    info <- exprSource e0
	    return $ A.Pi info tel e'

    -- Sorts
    toAbstract e@(C.Set _)    = flip A.Set 0 <$> exprSource e
    toAbstract e@(C.SetN _ n) = flip A.Set n <$> exprSource e
    toAbstract e@(C.Prop _)   = A.Prop <$> exprSource e

    -- Let
    toAbstract e0@(C.Let _ ds e) =
	bindToAbstract (LetDefs ds) $ \ds' ->
	do  e'   <- toAbstractCtx TopCtx e
	    info <- exprSource e0
	    return $ A.Let info ds' e'

    -- Parenthesis
    toAbstract (C.Paren _ e) = toAbstractCtx TopCtx e
	-- You could imagine remembering parenthesis. I don't really see the
	-- point though.

    -- Pattern things
    toAbstract e@(C.As _ _ _) = notAnExpression e
    toAbstract e@(C.Absurd _) = notAnExpression e

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
    toAbstract d = noTopLevelModule d	-- only for top-level modules.

instance BindToAbstract [C.Declaration] [A.Declaration] where
    bindToAbstract ds = bindToAbstract (niceDeclarations ds)

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
		    bindToAbstract (NewName $ nameDeclName x) $ \x ->
			ret (A.LetBind (LetSource c) x t e)
	    _	-> notAValidLetBinding d
	where
	    letToAbstract (CD.Clause top clhs (C.RHS rhs) []) = do
		p    <- parseLHS top clhs
		args <- lhsArgs p
		bindToAbstract args $ \args ->
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
	do  (x',cs') <- toAbstract (OldName $ nameDeclName x,cs)
	    ret $ A.FunDef (mkSourcedDefInfo x f p a ds) x' cs'

    -- Data definitions
    bindToAbstract (CD.DataDef r f p a x pars cons) ret = do
	(pars,cons) <- bindToAbstract pars $ \pars ->
		       bindToAbstract (map Constr cons) $ \cons ->
		       return (pars,cons)
	x' <- toAbstract (OldName $ nameDeclName x)
	bindToAbstract (map Constr cons) $ \_ ->
	    ret $ A.DataDef (mkRangedDefInfo x f p a r) x' pars cons

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list. Except we keep open
-- declarations. Oh well...
instance BindToAbstract NiceDeclaration [A.Declaration] where

    -- Axiom
    bindToAbstract (CD.Axiom r f p a x t) ret =
	do  t' <- toAbstractCtx TopCtx t
	    defineName p FunName f x $ \x' -> do
		ret [A.Axiom (mkRangedDefInfo x f p a r) x' t']
				-- we can easily reconstruct the original decl
				-- so we don't bother save it

    -- Primitive function
    bindToAbstract (PrimitiveFunction r f p a x t) ret = do
	t' <- toAbstractCtx TopCtx t
	defineName p FunName f x $ \x' ->
	    ret [A.Primitive (mkRangedDefInfo x f p a r) x' t']
			    -- we can easily reconstruct the original decl
			    -- so we don't bother save it

    -- Definitions (possibly mutual)
    bindToAbstract (NiceDef r cs ts ds) ret =
	bindToAbstract (ts,ds) $ \ (ts',ds') ->
	    ret [Definition (DeclInfo C.noName $ DeclSource cs) ts' ds']
		-- TODO: remember name


    -- TODO: what does an abstract module mean? The syntax doesn't allow it.
    bindToAbstract (NiceModule r p _ name@(C.QName x) tel ds) ret =
	do  (tel',ds',ns) <-
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
    bindToAbstract (NiceModule _ _ _ _ _ _) _ = __IMPOSSIBLE__

    bindToAbstract (NiceModuleMacro r p _ x tel e is) ret =
	case appView e of
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

    bindToAbstract (NiceOpen r x is) ret =
	openModule x is $ ret [A.Open $ DeclSource [C.Open r x is]]

    bindToAbstract (NicePragma r p) ret = do
	p <- toAbstract p
	ret [A.Pragma r p]

    bindToAbstract (NiceImport r x as is) ret =
	do  iface <- getModuleInterface x
	    x' <- toAbstract $ CModuleName x
	    importModule name iface is $
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
	    local (defName p ConName op x) $ ret ()
	where
	    a  = defAccess info
	    op = defOperator info
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
    bindToAbstract (LeftHandSide top lhs) ret = do
	p    <- parseLHS top lhs
	args <- lhsArgs p
	bindToAbstract args $ \args -> do
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
	    _		-> higherOrderPattern p0 p
	where
	    r = getRange p0
	    info = PatSource r $ \pr -> if appBrackets pr then ParenP r p0 else p0

    bindToAbstract p0@(OpAppP r op ps) ret =
	bindToAbstract (IdentP $ C.QName $ nameDeclName op)
			  $ \p ->
	bindToAbstract ps $ \ps ->
	    case p of
		ConP _ x as -> ret $ ConP info x (as ++ map (Arg NotHidden) ps)
		DefP _ x as -> ret $ DefP info x (as ++ map (Arg NotHidden) ps)
		_	    -> higherOrderPattern p0 (IdentP $ C.QName $ nameDeclName op)
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

