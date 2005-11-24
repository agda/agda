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

class ToAbstract concrete abstract | concrete -> abstract where
    toAbstract :: concrete -> ScopeM abstract

instance ToAbstract C.Expr A.Expr where
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
    toAbstract _    = undefined

