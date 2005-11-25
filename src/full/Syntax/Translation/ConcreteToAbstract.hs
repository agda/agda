{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances #-}

{-| Translation from "Syntax.Concrete" to "Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Syntax.Translation.ConcreteToAbstract where

import Control.Exception
import Data.Typeable

import Syntax.Concrete as C
import Syntax.Concrete.Pretty ()    -- TODO: only needed for Show for the exceptions
import Syntax.Abstract as A
import Syntax.Position
import Syntax.Common
import Syntax.Info
--import Syntax.Interface
import Syntax.Concrete.Definitions as CD
import Syntax.Concrete.Fixity
import Syntax.Scope

import Interaction.Imports

import Utils.Monad

#include "../../undefined.h"


{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

data ToAbstractException
	= HigherOrderPattern C.Pattern A.Pattern
	    -- ^ the concrete pattern is an application and the abstract
	    --	 pattern is the translation of the function part (and it's not
	    --	 a constructor pattern).
	| NotAModuleExpr C.Expr
	    -- ^ The expr was used in the right hand side of an implicit module
	    --	 definition, but it wasn't of the form @m Delta@.
    deriving (Typeable, Show)

higherOrderPattern p0 p = throwDyn $ HigherOrderPattern p0 p
notAModuleExpr e	= throwDyn $ NotAModuleExpr e

instance HasRange ToAbstractException where
    getRange (HigherOrderPattern p _) = getRange p
    getRange (NotAModuleExpr e)	      = getRange e

{--------------------------------------------------------------------------
    Translation
 --------------------------------------------------------------------------}

-- | Things that can be translated to abstract syntax are instances of this
--   class.
class ToAbstract concrete abstract | concrete -> abstract where
    toAbstract :: concrete -> ScopeM abstract

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

instance ToAbstract C.Expr A.Expr where

    -- Names
    toAbstract (Ident x) =
	do  qx <- resolveNameM x
	    case qx of
		VarName x'  -> return $
				Var (NameInfo
				    { bindingSite	= getRange x'
				    , concreteName	= x
				    , nameFixity	= defaultFixity
				    , nameAccess	= PrivateAccess
				    }
				   ) x'
		DefName d   ->
		    case kindOfName d of
			FunName  -> return $ Def info $ theName d
			ConName  -> return $ Con info $ theName d
			DataName -> return $ A.Data info $ theName d
		    where
			info = NameInfo { bindingSite   = getRange d
					, concreteName  = x
					, nameFixity    = fixity d
					, nameAccess    = access d
					}
		UnknownName	-> notInScope x

    -- Literals
    toAbstract (C.Lit l)    = return $ A.Lit l

    -- Meta variables
    toAbstract (C.QuestionMark r) =
	do  scope <- getScopeInfo
	    return $ A.QuestionMark $ MetaInfo { metaRange = r
					       , metaScope = scope
					       }
    toAbstract (C.Underscore r) =
	do  scope <- getScopeInfo
	    return $ A.Underscore $ MetaInfo { metaRange = r
					       , metaScope = scope
					       }

    -- Application
    toAbstract e@(C.App r h e1 e2) =
	uncurry (A.App (ExprSource e) h) <$> toAbstract (e1,e2)

    -- Infix application
    toAbstract e@(C.InfixApp _ _ _) =
	do  f <- getFixityFunction
	    -- Rotating an infix application always returns an infix application.
	    let C.InfixApp e1 op e2 = rotateInfixApp f e
	    (e1',op',e2') <- toAbstract (e1, Ident op, e2)
	    return $ A.App (ExprSource e) NotHidden
			   (A.App (ExprRange $ fuseRange e1' op')
				  NotHidden op' e1'
			   ) e2'    -- infix applications are never hidden

    -- Lambda
    toAbstract e0@(C.Lam r bs e) =
	bindToAbstract bs $ \ (b:bs') ->
	    do  e' <- toAbstract e
		return $ A.Lam (ExprSource e0) b $ foldr mkLam e' bs'
	where
	    mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

    -- Function types
    toAbstract e@(Fun r h e1 e2) =
	do  (e1',e2') <- toAbstract (e1,e2)
	    return $ A.Pi (ExprSource e)
			  (A.TypedBinding (getRange e1) h [noName] e1')
			  e2'

    toAbstract e0@(C.Pi b e) =
	bindToAbstract b $ \b' ->
	do  e' <- toAbstract e
	    return $ A.Pi (ExprSource e0) b' e'

    -- Sorts
    toAbstract e@(C.Set _)    = return $ A.Set (ExprSource e) 0
    toAbstract e@(C.SetN _ n) = return $ A.Set (ExprSource e) n
    toAbstract e@(C.Prop _)   = return $ A.Prop (ExprSource e)

    -- Let
    toAbstract e0@(C.Let _ ds e) =
	bindToAbstract ds $ \ds' ->
	do  e' <- toAbstract e
	    return $ A.Let (ExprSource e0) ds' e'

    -- Parenthesis
    toAbstract (C.Paren _ e) = toAbstract e
	-- You could imagine remembering parenthesis. I don't really see the
	-- point though.

instance BindToAbstract C.LamBinding A.LamBinding where
    bindToAbstract (C.DomainFree h x) ret =
	bindVariable x $ ret (A.DomainFree h x)
    bindToAbstract (C.DomainFull tb) ret =
	bindToAbstract tb $ \tb' -> ret (A.DomainFull tb')

instance BindToAbstract C.TypedBinding A.TypedBinding where
    bindToAbstract (C.TypedBinding r h xs t) ret =
	do  t' <- toAbstract t
	    bindVariables xs $ ret (A.TypedBinding r h xs t')

instance BindToAbstract [C.Declaration] [A.Declaration] where
    bindToAbstract ds = bindToAbstract (niceDeclarations ds)

instance BindToAbstract [NiceDeclaration] [A.Declaration] where
    bindToAbstract [] ret = ret []
    bindToAbstract (x:xs) ret =
	bindToAbstract (x,xs) $ \ (y,ys) -> ret (y ++ ys)

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list.
instance BindToAbstract NiceDeclaration [A.Declaration] where

    -- Axiom
    bindToAbstract (CD.Axiom r f a x t) ret =
	do  t' <- toAbstract t
	    defineName a FunName f x $
		ret [A.Axiom info x t']
	where
	    info = DefInfo { defFixity = f
			   , defAccess = a
			   , defInfo   = DeclRange r
				-- we can easily reconstruct the original decl
				-- so we don't bother save it
			   }

    -- Function definition
    bindToAbstract (CD.FunDef r ds f a x mt cs) ret =
	do  mt' <- toAbstract mt
	    defineName a FunName f x $
		do  cs' <- toAbstract cs
		    ret [A.FunDef info x mt' cs']
	where
	    info = DefInfo { defFixity = f
			   , defAccess = a
			   , defInfo   = DeclSource ds
			   }

    -- Data declaration
    bindToAbstract (NiceData r f a x tel e cons) ret =
	do  (tel',e',cons')
		<- bindToAbstract tel $ \tel' ->
		    do	e'    <- toAbstract e
			cons' <- defineName a DataName f x
				 $ toAbstract $ map Constr cons
			return (tel', e', cons')
	    defineName a DataName f x $
		bindToAbstract (map Constr cons') $ \_ ->
		ret [DataDecl info x tel' e' cons']
	where
	    info = DefInfo { defAccess = a
			   , defFixity = f
			   , defInfo   = DeclRange r
			   }

    bindToAbstract (NiceAbstract r ds) ret =
	bindToAbstract ds $ \ds' ->
	    ret [A.Abstract (DeclRange r) ds']

    bindToAbstract (NiceMutual r ds) ret =  -- TODO: this is wrong
	bindToAbstract ds $ \ds' ->
	    ret [A.Mutual (DeclRange r) ds']

    bindToAbstract (NiceModule r a (QName x) tel ds) ret =
	do  (tel',ds',ns) <-
		insideModule (QName x) $
		bindToAbstract (tel,ds) $ \ (tel',ds') ->
		    do	ns <- currentNameSpace
			return (tel',ds',ns)
	    let m = ModuleInfo { moduleArity	= length tel
			       , moduleAccess	= a
			       , moduleContents = ns
			       }
	    defineModule x m $
		ret [A.Module info (QName x) tel' ds']
	where
	    info = DefInfo { defAccess = a
			   , defFixity = defaultFixity
			   , defInfo   = DeclRange r
			   }

    -- Top-level modules are translated with toAbstract.
    bindToAbstract (NiceModule _ _ _ _ _) _ = __IMPOSSIBLE__

    bindToAbstract (NiceModuleMacro r a x tel e is) ret =
	case appView e of
	    AppView (Ident m) args  ->
		bindToAbstract tel $ \tel' ->
		    do  args' <- toAbstract args
			implicitModule x a (length tel) m is $
			    ret [ModuleDef info x tel' m args']
		where
		    info = DefInfo { defAccess = a
				   , defFixity = defaultFixity	-- modules don't have fixities
				   , defInfo   = DeclRange r
				   }
		    
	    _	-> notAModuleExpr e

    bindToAbstract (NiceOpen r x is) ret = openModule x is $ ret []

    bindToAbstract (NiceImport r x as is) ret =
	do  iface <- getModuleInterface x
	    importModule name iface is $ ret [A.Import (DeclRange r) x]
	where
	    name = maybe x QName as

newtype Constr a = Constr a

instance ToAbstract (Constr CD.NiceDeclaration) A.Declaration where
    toAbstract (Constr (CD.Axiom r f a x t)) =
	do  t' <- toAbstract t
	    return (A.Axiom info x t')
	where
	    info = DefInfo { defAccess = a
			   , defFixity = f
			   , defInfo   = DeclRange r
			   }

    bindToAbstract _ _ = __IMPOSSIBLE__    -- a constructor is always an axiom

instance ToAbstract CD.Clause A.Clause where
    toAbstract (CD.Clause lhs rhs wh) =
	bindToAbstract lhs $ \lhs' ->	-- the order matters here!
	bindToAbstract wh  $ \wh'  ->
	    do	rhs' <- toAbstract rhs
		return $ A.Clause lhs' rhs' wh'

instance BindToAbstract C.LHS A.LHS where
    bindToAbstract lhs@(C.LHS _ _ x as) ret =
	bindToAbstract as $ \as' ->
	ret (A.LHS (LHSSource lhs) x as')

instance BindToAbstract c a => BindToAbstract (Arg c) (Arg a) where
    bindToAbstract (Arg h e) ret = bindToAbstract e $ ret . Arg h

instance ToAbstract c a => ToAbstract (Arg c) (Arg a) where
    toAbstract (Arg h e) = Arg h <$> toAbstract e

instance BindToAbstract C.Pattern A.Pattern where
    bindToAbstract p@(C.IdentP x) ret =
	do  rx <- resolvePatternNameM x	-- only returns VarName, ConName or UnknownName
	    case rx of
		VarName y   -> bindVariable y $ ret (VarP y)
		DefName d | kindOfName d == ConName
			    -> ret $ ConP (PatSource p) (theName d) []
		UnknownName -> notInScope x
		_	    -> __IMPOSSIBLE__
    bindToAbstract p0@(AppP h p q) ret =
	bindToAbstract (p,q) $ \(p',q') ->
	case p' of
	    ConP _ x as -> ret $ ConP (PatSource p0) x (as ++ [Arg h q'])
	    _		-> higherOrderPattern p0 p'
    bindToAbstract p0@(InfixAppP _ _ _) ret =
	do  f <- getFixityFunction
	    case rotateInfixAppP f p0 of
		InfixAppP p op q ->
		    bindToAbstract (C.IdentP op) $ \pop ->
		    case pop of
			ConP _ op' []   ->
			    bindToAbstract (p,q) $ \ (p',q') ->
			    ret $ ConP (PatSource p0) op'
				$ map (Arg NotHidden) [p',q']
			_ -> higherOrderPattern p0 pop
		_ -> __IMPOSSIBLE__ -- rotating an infix app produces an infix app
    bindToAbstract p@(C.WildP _) ret  = ret $ A.WildP (PatSource p)
    bindToAbstract (C.ParenP _ p) ret = bindToAbstract p ret

