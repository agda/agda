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
import Control.Monad.Reader hiding (mapM)
import Data.Typeable
import Data.Traversable (mapM)

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
import Syntax.Strict

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

setContextCPS :: Precedence -> (a -> ScopeM b) ->
		 ((a -> ScopeM b) -> ScopeM b) -> ScopeM b
setContextCPS ctx ret f = do
    ctx' <- getContextPrecedence
    setContext ctx $ f $ setContext ctx' . ret

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
    toAbstract (NewName x) = abstractName x

instance BindToAbstract NewName A.Name where
    bindToAbstract x ret =
	do  x' <- toAbstract x
	    bindVariable x' $ ret x'

varExpr :: C.QName -> A.Name -> A.Expr
varExpr x y =
    Var (NameInfo
	{ bindingSite  = getRange y
	, concreteName = x
	, nameFixity   = defaultFixity
	, nameAccess   = PrivateAccess
	}
       ) (setRange (getRange x) y)
    where
	-- TODO: move somewhere else and generalise.
	setRange r (A.Name i (C.Name _ xs)) = A.Name i (C.Name r xs)

nameExpr :: C.QName -> DefinedName -> A.Expr
nameExpr x d = mk (kindOfName d) info $ theName d
    where
	mk FunName = Def
	mk ConName = Con

	info = NameInfo { bindingSite  = getRange d
			, concreteName = x
			, nameFixity   = fixity d
			, nameAccess   = access d
			}

instance ToAbstract OldQName A.Expr where
    toAbstract (OldQName x) =
	do  qx <- resolveName x
	    case qx of
		VarName x'  -> return $ varExpr x x'
		DefName d   -> return $ nameExpr x d
		UnknownName -> notInScope x

data APatName = VarPatName A.Name
	      | ConPatName DefinedName
	      | DefPatName DefinedName

instance BindToAbstract PatName APatName where
    bindToAbstract (PatName x) ret = do
	rx <- resolvePatternNameM x
	case rx of
	    VarName y   -> bindVariable y $ ret $ VarPatName y
	    DefName d
		| kindOfName d == ConName -> do
		    ret $ ConPatName d
		| kindOfName d == FunName -> do
		    ret $ DefPatName d
	    UnknownName -> notInScope x
	    _		-> __IMPOSSIBLE__

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

type ScopeMCPS a = forall r. (a -> ScopeM r) -> ScopeM r

-- | To avoid duplicating a lot of code between the 'ToAbstract' and
-- 'BindToAbstract' instances for expressions, we implement a general
-- (continuation passing) translation function parameterised over what to do
-- for names.
-- Except the BindToAbstract instance was removed. Doesn't hurt to keep the
-- more general version though.
exprToAbstract :: (C.QName -> ScopeMCPS A.Expr) -> C.Expr -> ScopeMCPS A.Expr
exprToAbstract ident e ret =
    traceCallCPS (ScopeCheckExpr e) ret $ \ret -> case e of
    -- Names
	Ident x	-> ident x ret

    -- Literals
	C.Lit l	-> ret $ A.Lit l

    -- Meta variables
	C.QuestionMark r n -> do
	    scope <- getScopeInfo
	    ret $ A.QuestionMark $ MetaInfo { metaRange  = r
					    , metaScope  = scope
					    , metaNumber = n
					    }
	C.Underscore r n -> do
	    scope <- getScopeInfo
	    ret $ A.Underscore $ MetaInfo { metaRange  = r
					  , metaScope  = scope
					  , metaNumber = n
					  }

    -- Raw application
	C.RawApp r es -> do
	    e <- parseApplication es
	    exprToAbstract ident e ret

    -- Application
	C.App r e1 e2 ->
	    let (arg, e2') = case e2 of
		    Arg h (Named Nothing  x) -> (Arg h . unnamed, x)
		    Arg h (Named (Just s) x) -> (Arg h . named s, x)
	    in
	    exprToAbstractCtx FunctionCtx ident e1  $ \e1 ->
	    exprToAbstractCtx ArgumentCtx ident e2' $ \e2 -> do
	    info <- exprSource e
	    ret $ A.App info e1 (arg e2)

    -- Operator application

	C.OpApp r op es -> toAbstractOpApp r ident op es ret

    -- Malplaced hidden argument
	C.HiddenArg _ _ -> nothingAppliedToHiddenArg e

    -- Lambda
	e0@(C.Lam r bs e) ->
	    bindToAbstract bs $ \(b:bs') ->
	    exprToAbstractCtx TopCtx ident e $ \e' -> do
	    info <- exprSource e0
	    ret $ A.Lam info b $ foldr mkLam e' bs'
	    where
		mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

    -- Function types
	C.Fun r e1 e2 ->
	    let (h, ctx, e1') = case e1 of
		    C.HiddenArg _ e1 -> (Arg Hidden, TopCtx, namedThing e1)
		    _		     -> (Arg NotHidden, FunctionSpaceDomainCtx, e1)
	    in
	    exprToAbstractCtx ctx ident e1'   $ \e1 ->
	    exprToAbstractCtx TopCtx ident e2 $ \e2 -> do
	    info <- exprSource e
	    ret $ A.Fun info (h e1) e2

	e0@(C.Pi tel e) ->
	    bindToAbstract tel $ \tel ->
	    exprToAbstractCtx TopCtx ident e $ \e -> do
	    info <- exprSource e0
	    ret $ A.Pi info tel e

    -- Sorts
	C.Set _    -> ret =<< flip A.Set 0 <$> exprSource e
	C.SetN _ n -> ret =<< flip A.Set n <$> exprSource e
	C.Prop _   -> ret =<< A.Prop <$> exprSource e

    -- Let
	e0@(C.Let _ ds e) ->
	    bindToAbstract (LetDefs ds) $ \ds' ->
	    exprToAbstractCtx TopCtx ident e $ \e -> do
	    info <- exprSource e0
	    ret $ A.Let info ds' e

    -- Parenthesis
	C.Paren _ e -> exprToAbstractCtx TopCtx ident e ret

    -- Pattern things
	C.As _ _ _ -> notAnExpression e
	C.Dot _ _  -> notAnExpression e
	C.Absurd _ -> notAnExpression e

-- | Same as 'exprToAbstract' but setting the context precedence.
exprToAbstractCtx :: Precedence -> (C.QName -> ScopeMCPS A.Expr) -> C.Expr -> ScopeMCPS A.Expr
exprToAbstractCtx ctx ident e ret = setContextCPS ctx ret $ exprToAbstract ident e


instance ToAbstract C.Expr A.Expr where
    toAbstract e = exprToAbstract (\x ret -> ident x ret) e return
	where
	    ident x ret = ret =<< toAbstract (OldQName x)
    
-- Expressions in dot patterns might bind variables, so we need an instance for
-- this.
-- They can't anymore. So we remove this instance.
{-
instance BindToAbstract C.Expr A.Expr where
    bindToAbstract = exprToAbstract (\x ret -> ident x ret)
	where
	    ident x ret =
		bindToAbstract (PatName x) $ \px ->
		case px of
		    VarPatName y -> ret $ varExpr x y
		    ConPatName d -> ret $ nameExpr x d
		    DefPatName d -> ret $ nameExpr x d
-}

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

newtype TopLevel a = TopLevel a

-- Top-level declarations are always (import|open)* module
instance ToAbstract (TopLevel [C.Declaration]) ([A.Declaration], ScopeInfo) where
    toAbstract (TopLevel ds) = case splitAt (length ds - 1) ds of
	(ds', [C.Module r x tel ds]) ->
	    bindToAbstract ds'	    $ \ds' ->
	    insideModule x	    $
	    bindToAbstract (tel,ds) $ \(tel,ds) -> do    -- order matter!
		scope <- getScopeInfo
		x' <- toAbstract $ CModuleName x
		return (ds' ++ [A.Module info x' tel ds], scope)
	    where
		info = mkRangedModuleInfo PublicAccess ConcreteDef r
	_ -> __IMPOSSIBLE__

instance BindToAbstract [C.Declaration] [A.Declaration] where
    bindToAbstract ds ret = do
	ds <- liftIO $ return $!! niceDeclarations ds
	bindToAbstract ds ret

instance BindToAbstract [NiceDeclaration] [A.Declaration] where
    bindToAbstract [] ret = ret []
    bindToAbstract (x:xs) ret =
	bindToAbstract (x,xs) $ \ (y,ys) -> ret (y ++ ys)

newtype LetDefs = LetDefs [C.Declaration]
newtype LetDef = LetDef NiceDeclaration

instance BindToAbstract LetDefs [A.LetBinding] where
    bindToAbstract (LetDefs ds) ret = do
	ds <- liftIO $ return $!! niceDeclarations ds
	bindToAbstract (map LetDef ds) ret

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
	NiceModule r p a name@(C.QName x) tel ds -> do
	    (tel',ds',ns) <-
		insideModule name $
		bindToAbstract (tel,ds) $ \ (tel',ds') ->
		    do	ns <- currentNameSpace
			return (tel',ds',ns)
	    let m = ModuleScope { moduleArity	 = length tel
			        , moduleAccess	 = p
			        , moduleContents = ns
			        }
	    name' <- toAbstract $ CModuleName name
	    defineModule x m $
		ret [A.Module (mkRangedModuleInfo p a r)
			      name' tel' ds']

    -- Top-level modules are translated with toAbstract.
	NiceModule _ _ _ _ _ _ -> __IMPOSSIBLE__

	NiceModuleMacro r p a x tel e is -> case appView e of
	    AppView (Ident m) args  ->
		bindToAbstract tel $ \tel' ->
		    do	(x',m',args') <- toAbstract ( CModuleName $ C.QName x
						    , CModuleNameRef m
						    , args
						    )
			implicitModule x p (length tel) m is $
			    ret [ ModuleDef (mkSourcedModuleInfo p a
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
		ret [A.Import (mkSourcedModuleInfo PublicAccess ConcreteDef [C.Import r x as is]) x']
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
	    ConPatName d -> ret $ ConP (PatSource (getRange p) $ const p) (theName d) []
	    DefPatName d -> ret $ DefP (PatSource (getRange p) $ const p) (theName d) []

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
    bindToAbstract p0@(C.DotP r e) ret = ret $ A.DotP info e	-- we have to do dot patterns at the end
	where info = PatSource r $ \_ -> p0
    bindToAbstract p0@(C.AbsurdP r) ret = ret (A.AbsurdP info)
	where
	    info = PatSource r $ \_ -> p0

-- Helpers for OpApp case

  -- let's deal with the binary case (there should be no special casing
  -- in future.)
toAbstractOpApp :: Range -> (C.QName -> ScopeMCPS A.Expr) -> C.Name -> [C.Expr] -> ScopeMCPS A.Expr
toAbstractOpApp r ident op@(C.Name _ xs) es ret = do
    f  <- getFixity (C.QName op)
    op <- toAbstract (OldQName $ C.QName op) -- op-apps cannot bind the op
    left f xs es $ \es -> ret $ foldl app op es
    where
	app e arg = A.App (ExprRange (fuseRange e arg)) e
		  $ Arg NotHidden $ unnamed arg

	left f (Hole : xs) (e : es) ret =
	    exprToAbstractCtx (LeftOperandCtx f) ident e $ \e ->
	    inside f xs es $ \es ->
	    ret (e : es)
	left f (Id _ : xs) es ret = inside f xs es ret
	left f (Hole : _) [] _	  = __IMPOSSIBLE__
	left f [] _ _		  = __IMPOSSIBLE__

	inside f [x]	      es      ret = right f x es ret
	inside f (Id _ : xs)  es      ret = inside f xs es ret
	inside f (Hole : xs) (e : es) ret =
	    exprToAbstractCtx InsideOperandCtx ident e $ \e ->
	    inside f xs es $ \es ->
	    ret (e : es)
	inside _ (Hole : _) [] _ = __IMPOSSIBLE__
	inside _ [] _ _		 = __IMPOSSIBLE__

	right f Hole [e] ret =
	    exprToAbstractCtx (RightOperandCtx f) ident e $ \e ->
	    ret [e]
	right _ (Id _) [] ret = ret []
	right _ Hole _ _      = __IMPOSSIBLE__
	right _ (Id _) _ _    = __IMPOSSIBLE__

