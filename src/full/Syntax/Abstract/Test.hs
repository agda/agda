
{-| This module contains functions to test the correctness of functions
    operating on abstract syntax. At the moment it contains function to
    check if two pieces of abstract syntax are equal.
-}
module Syntax.Abstract.Test where

import Syntax.Position
import Syntax.Common
import Syntax.Abstract
import Syntax.Info
import Syntax.Literal
import Syntax.Abstract.Name

-- Comparisons ------------------------------------------------------------

data Comparison	= Equal | Unequal Range Range

fromBool :: (HasRange a, HasRange b) => a -> b -> Bool -> Comparison
fromBool _ _ True  = Equal
fromBool x y False = Unequal (getRange x) (getRange y)

unequal :: (HasRange a, HasRange b) => a -> b -> Comparison
unequal x y = fromBool x y False

infix  5 ===
infixr 4 &&&

(&&&) :: Comparison -> Comparison -> Comparison
Equal	      &&& c = c
Unequal r1 r2 &&& _ = Unequal r1 r2

-- The equal class --------------------------------------------------------

class Equal a where
    (===) :: a -> a -> Comparison

-- General instances ------------------------------------------------------

instance (Equal a, Equal b) => Equal (a,b) where
    (x,y) === (z,w) = x === z &&& y === w

instance (Equal a, Equal b, Equal c) => Equal (a,b,c) where
    (x,y,z) === (a,b,c) = (x,(y,z)) === (a,(b,c))

instance (Equal a, Equal b, Equal c, Equal d) => Equal (a,b,c,d) where
    (x,y,z,w) === (a,b,c,d) = ((x,y),(z,w)) === ((a,b),(c,d))

instance (Equal a, Equal b, Equal c, Equal d, Equal e) => Equal (a,b,c,d,e) where
    (x,y,z,w,v) === (a,b,c,d,e) = ((x,y),(z,w,v)) === ((a,b),(c,d,e))

instance Equal a => Equal [a] where
    xs === ys = foldr (&&&) Equal $ zipWith (===) xs ys

-- Info instances ---------------------------------------------------------

instance Equal NameInfo where
    i === j = fromBool i j $ nameFixity i == nameFixity j
			  && nameAccess i == nameAccess j

instance Equal DefInfo where
    i === j = fromBool i j $ defFixity i == defFixity j
			  && defAccess i == defAccess j

instance Equal ModuleInfo where
    i === j = fromBool i j $ minfoAccess i == minfoAccess j

instance Equal DeclSource where
    i === j = fromBool i j $ i == j

-- Simple instances -------------------------------------------------------

instance Equal Literal where
    l === k = fromBool l k $ l == k

instance Equal Name where
    x === y = fromBool x y $ x == y

instance Equal QName where
    x === y = fromBool x y $ x == y

instance Equal ModuleName where
    x === y = fromBool x y $ x == y

-- Expression instances ---------------------------------------------------

instance Equal Expr where
    Var i x	    === Var j y		= (i,x) === (j,y)
    Def i x	    === Def j y		= (i,x) === (j,y)
    Con i x	    === Con j y		= (i,x) === (j,y)
    Lit l	    === Lit k		= l === k
    QuestionMark _  === QuestionMark _	= Equal
    Underscore _    === Underscore _	= Equal
    App _ e1 e2	    === App _ d1 d2	= (e1,e2) === (d1,d2)
    Lam _ b1 e1	    === Lam _ b2 e2	= (b1,e1) === (b2,e2)
    Pi _ b1 e1	    === Pi _ b2 e2	= (b1,e1) === (b2,e2)
    Fun _ e1 e2	    === Fun _ d1 d2	= (e1,e2) === (d1,d2)
    Set i n	    === Set j m		= fromBool i j $ n == m
    Prop _	    === Prop _		= Equal
    Let _ ds e	    === Let _ ds' e'	= (ds,e) === (ds',e')
    e1		    === e2		= unequal e1 e2

-- Binding instances ------------------------------------------------------

instance Equal LamBinding where
    DomainFree h x === DomainFree h' y  = fromBool x y (h == h') &&& x === y
    DomainFull b   === DomainFull b'	= b === b'
    b1		   === b2		= unequal b1 b2

instance Equal TypedBinding where
    TypedBinding r h xs e === TypedBinding r' h' ys e'	= fromBool r r' (h == h')
							    &&& (xs,e) === (ys,e')

instance Equal Declaration where
    Axiom i x s			=== Axiom j y t			= (i,x,s) === (j,y,t)
    Definition _ ts ds		=== Definition _ ts' ds'	= (ts,ds) === (ts',ds')
    Module i x tel ds		=== Module j y tel' ds'		= (i,x,tel,ds) === (j,y,tel',ds')
    ModuleDef i x tel y args	=== ModuleDef j z tel' w args'	= (i,x,tel,y,args) === (j,z,tel',w,args')
    Import _ x			=== Import _ y			= x === y
    Open _			=== Open _			= Equal
    d				=== d'				= unequal d d'

instance Equal Definition where
    FunDef i x cs	=== FunDef j y cs'	= (i,x,cs) === (j,y,cs')
    DataDef i x bs cs	=== DataDef j y bs' cs'	= (i,x,bs,cs) === (j,y,bs',cs')
    d			=== d'			= unequal d d'

instance Equal LetBinding where
    LetBind _ x t v === LetBind _ y s u = (x,t,v) === (y,s,u)

instance Equal Clause where
    Clause lhs rhs wh === Clause lhs' rhs' wh'	= (lhs,rhs,wh) === (lhs',rhs',wh')

-- Left hand side instances -----------------------------------------------

instance (HasRange a, Equal a) => Equal (Arg a) where
    Arg h x === Arg h' y    = fromBool x y (h == h') &&& x === y

instance Equal LHS where
    LHS _ x args === LHS _ y args'   = (x,args) === (y,args')

instance Equal Pattern where
    VarP x	    === VarP y		= x === y
    ConP _ x args   === ConP _ y args'	= (x,args) === (y,args')
    WildP _	    === WildP _		= Equal
    p		    === q		= unequal p q

