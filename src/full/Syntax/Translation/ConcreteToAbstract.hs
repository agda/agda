{-# OPTIONS -fglasgow-exts #-}

{-| Translation from "Syntax.Concrete" to "Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Syntax.Translation.ConcreteToAbstract where

import Syntax.Concrete as C
import Syntax.Abstract as A
import Syntax.Position
import Syntax.Common
import Syntax.Info
--import Syntax.Interface
--import Syntax.Concrete.Definitions
--import Syntax.Concrete.Fixity
import Syntax.Scope

import Utils.Monad

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

instance ToAbstract c a => ToAbstract [c] [a] where
    toAbstract = mapM toAbstract 

instance ToAbstract C.Expr A.Expr where

    -- Names
    toAbstract (Ident x) =
	do  qx <- resolveName x
	    return $
		case qx of
		    VarName x'  -> Var (NameInfo
					{ bindingSite	= getRange x'
					, concreteName	= x
					, nameFixity	= defaultFixity
					, nameAccess	= PrivateAccess
					}
				       ) x'
		    DefName d   ->
			case kindOfName d of
			    FunName  -> Def info $ theName d
			    ConName  -> Con info $ theName d
			    DataName -> A.Data info $ theName d
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

    toAbstract _    = undefined

