{-# OPTIONS -fallow-overlapping-instances #-}

module TypeChecking.Serialise where

import Syntax.Concrete.Name as C
import Syntax.Abstract.Name as A
import Syntax.Internal
import Syntax.Scope
import Syntax.Position
import Syntax.Common
import Syntax.Fixity
import Syntax.Literal

import TypeChecking.Monad
import TypeChecking.Interface

import Utils.Serialise
import Utils.Tuple

instance Serialisable ModuleName where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry MName
	    des = mnameId /\ mnameConcrete

instance Serialisable C.Name where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry C.Name
	    des (C.Name r xs) = (r,xs)

instance Serialisable C.NamePart where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = maybe C.Hole C.Id
	    des Hole   = Nothing
	    des (Id s) = Just s

instance Serialisable Range where
    serialiser = returnS $ Range p p -- mapS (IFun con des) serialiser
	where
	    p = Pn "<imported>" 0 0
	    con = uncurry Range
	    des = rStart /\ rEnd

instance Serialisable Position where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = maybe NoPos (uncurry $ uncurry Pn)
	    des NoPos	   = Nothing
	    des (Pn f l c) = Just ((f,l),c)

instance Serialisable C.QName where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = either C.QName (uncurry C.Qual)
	    des (C.QName x)  = Left x
	    des (C.Qual m x) = Right (m,x)

instance Serialisable ModuleScope where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry $ uncurry ModuleScope
	    des = (moduleArity /\ moduleAccess) /\ moduleContents

instance Serialisable Access where
    serialiser = mapS (IFun con des) serialiser
	where
	    con True  = PublicAccess
	    con False = PrivateAccess
	    des PublicAccess  = True
	    des PrivateAccess = False

instance Serialisable NameSpace where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry $ uncurry NSpace
	    des = (moduleName /\ definedNames ) /\ modules

instance Serialisable DefinedName where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry $ uncurry $ uncurry DefinedName 
	    des = ((access /\ kindOfName) /\ fixity) /\ theName

instance Serialisable KindOfName where
    serialiser = mapS (IFun con des) serialiser
	where
	    con True  = FunName
	    con False = ConName
	    des FunName = True
	    des ConName = False

instance Serialisable Fixity where
    serialiser = mapS (IFun con des) serialiser
	where
	    con ('l',r,n) = LeftAssoc r n
	    con ('r',r,n) = RightAssoc r n
	    con ('n',r,n) = NonAssoc r n
	    con _	    = error $ "deserialise Fixity: no parse"
	    des (LeftAssoc  r n) = ('l',r,n)
	    des (RightAssoc r n) = ('r',r,n)
	    des (NonAssoc   r n) = ('n',r,n)

instance Serialisable A.QName where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry $ uncurry A.QName
	    des = (qnameName /\ qnameModule) /\ qnameConcrete

instance Serialisable A.Name where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry A.Name
	    des = nameId /\ nameConcrete

instance Serialisable NameId where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = NameId
	    des (NameId n) = n

instance Serialisable ModuleDef where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry $ uncurry $ uncurry ModuleDef
	    des = ((mdefName /\ mdefTelescope) /\ mdefNofParams) /\ mdefDefs

instance Serialisable a => Serialisable (Arg a) where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry Arg
	    des = argHiding /\ unArg

instance Serialisable Hiding where
    serialiser = mapS (IFun con des) serialiser
	where
	    con True	  = Hidden
	    con False	  = NotHidden
	    des Hidden	  = True
	    des NotHidden = False

instance Serialisable Type where
    serialiser = mapS (IFun con des) serialiser
	where
	    con (s,t) = El s t
	    des (El s t) = (s,t)

instance Serialisable MetaId where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = MetaId 
	    des (MetaId n) = n

instance Serialisable a => Serialisable (Blocked a) where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry Blocked
	    des = blockingMeta /\ blockee

instance Serialisable a => Serialisable (Abs a) where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry Abs
	    des = absName /\ absBody

instance Serialisable Term where
    serialiser = bindS code serialiser $ \c -> case c of
	    'V' -> mapS (uncurry Var `IFun` unVar) serialiser
	    'L' -> mapS (uncurry Lam `IFun` unLam) serialiser
	    'I' -> mapS (Lit `IFun` unLit) serialiser
	    'D' -> mapS (uncurry Def `IFun` unDef) serialiser
	    'C' -> mapS (uncurry Con `IFun` unCon) serialiser
	    'P' -> mapS (uncurry Pi `IFun` unPi) serialiser
	    'F' -> mapS (uncurry Fun `IFun` unFun) serialiser
	    'S' -> mapS (Sort `IFun` unSort) serialiser
	    'B' -> mapS (BlockedV `IFun` unBlockedV) serialiser
	    'M' -> mapS (uncurry MetaV `IFun` unMetaV) serialiser
	    _	-> error $ "deserialise Term: no parse"
	where
	    code t = case t of
		Var _ _    -> 'V'
		Lam  _ _   -> 'L'
		Lit _	   -> 'I'
		Def _ _    -> 'D'
		Con _ _    -> 'C'
		Pi _ _	   -> 'P'
		Fun _ _    -> 'F'
		Sort _	   -> 'S'
		MetaV _ _  -> 'M'
		BlockedV _ -> 'B'

	    unVar      x = let Var	a b = x in (a,b)
	    unLam      x = let Lam	a b = x in (a,b)
	    unDef      x = let Def	a b = x in (a,b)
	    unCon      x = let Con	a b = x in (a,b)
	    unLit      x = let Lit	a   = x in a
	    unPi       x = let Pi	a b = x in (a,b)
	    unFun      x = let Fun	a b = x in (a,b)
	    unSort     x = let Sort	a   = x in a
	    unMetaV    x = let MetaV	a b = x in (a,b)
	    unBlockedV x = let BlockedV a   = x in a

instance Serialisable Sort where
    serialiser = bindS code serialiser $ \c -> case c of
	    'T' -> mapS (Type `IFun` unType) serialiser
	    'P' -> returnS Prop
	    'L' -> mapS (uncurry Lub `IFun` unLub) serialiser
	    'S' -> mapS (Suc `IFun` unSuc) serialiser
	    'M' -> mapS (MetaS `IFun` unMetaS) serialiser
	    _	-> error $ "deserialise Sort: no parse"
	where
	    code s = case s of
		Type _	-> 'T'
		Prop	-> 'P'
		Lub _ _ -> 'L'
		Suc _	-> 'S'
		MetaS _ -> 'M'

	    unType  x = let Type  a   = x in a
	    unSuc   x = let Suc   a   = x in a
	    unLub   x = let Lub   a b = x in (a,b)
	    unMetaS x = let MetaS a   = x in a

instance Serialisable Literal where
    serialiser = bindS code serialiser $ \c -> case c of
	    'n' -> mapS (uncurry LitInt `IFun` unInt) serialiser
	    'f' -> mapS (uncurry LitFloat `IFun` unFloat) serialiser
	    's' -> mapS (uncurry LitString `IFun` unString) serialiser
	    'c' -> mapS (uncurry LitChar `IFun` unChar) serialiser
	    _	-> error $ "deserialise Literal: no parse"
	where
	    code s = case s of
		LitInt _ _    -> 'n'
		LitFloat _ _  -> 'f'
		LitString _ _ -> 's'
		LitChar _ _   -> 'c'

	    unInt    x = let LitInt    a b = x in (a,b)
	    unFloat  x = let LitFloat  a b = x in (a,b)
	    unString x = let LitString a b = x in (a,b)
	    unChar   x = let LitChar   a b = x in (a,b)

instance Serialisable Integer where
    serialiser = mapS (IFun read show) serialiser

instance Serialisable Double where
    serialiser = mapS (IFun read show) serialiser

instance Serialisable Definition where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry $ uncurry Defn
	    des = (defType /\ defFreeVars ) /\ theDef

instance Serialisable Defn where
    serialiser = bindS code serialiser $ \c -> case c of
	    'A' -> returnS Axiom
	    'F' -> mapS (uncurry Function `IFun` unFunction) serialiser
	    'D' -> mapS (datatype `IFun` unData) serialiser
	    'C' -> mapS (cons `IFun` unCons) serialiser
	    'P' -> mapS (uncurry Primitive `IFun` unPrim) serialiser
	    _	-> error $ "deserialise Defn: no parse"
	where
	    code s = case s of
		Axiom		  -> 'A'
		Function _ _	  -> 'F'
		Datatype _ _ _ _  -> 'D'
		Constructor _ _ _ -> 'C'
		Primitive _ _	  -> 'P'

	    datatype ((a,b),(c,d)) = Datatype a b c d
	    cons (a,b,c)	     = Constructor a b c

	    unFunction x = let Function    a b	   = x in (a,b)
	    unData     x = let Datatype    a b c d = x in ((a,b),(c,d))
	    unCons     x = let Constructor a b c   = x in (a,b,c)
	    unPrim     x = let Primitive   a b	   = x in (a,b)

instance Serialisable IsAbstract where
    serialiser = mapS (IFun con des) serialiser
	where
	    con True	      = AbstractDef
	    con False	      = ConcreteDef
	    des AbstractDef = True
	    des ConcreteDef = False

instance Serialisable Clause where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry Clause
	    des (Clause ps b) = (ps,b)

instance Serialisable ClauseBody where
    serialiser = bindS code serialiser $ \c -> case c of
	    'b' -> mapS (Bind `IFun` unBind) serialiser
	    'n' -> mapS (NoBind `IFun` unNoBind) serialiser
	    'o' -> mapS (Body `IFun` unBody) serialiser
	    '-' -> returnS NoBody
	    _	-> error $ "deserialise ClauseBody: no parse"
	where
	    code s = case s of
		Bind _	 -> 'b'
		NoBind _ -> 'n'
		Body _	 -> 'o'
		NoBody	 -> '-'

	    unBind   x = let Bind   a = x in a
	    unNoBind x = let NoBind a = x in a
	    unBody   x = let Body   a = x in a

instance Serialisable Pattern where
    serialiser = bindS code serialiser $ \c -> case c of
	    'v' -> mapS (VarP `IFun` unVarP) serialiser
	    'c' -> mapS (uncurry ConP `IFun` unConP) serialiser
	    'l' -> mapS (LitP `IFun` unLitP) serialiser
	    '-' -> returnS AbsurdP
	    _	-> error $ "deserialise Pattern: no parse"
	where
	    code s = case s of
		VarP _	 -> 'v'
		ConP _ _ -> 'c'
		LitP _	 -> 'l'
		AbsurdP  -> '-'

	    unVarP x = let VarP a   = x in a
	    unLitP x = let LitP a   = x in a
	    unConP x = let ConP a b = x in (a,b)

instance Serialisable a => Serialisable (Builtin a) where
    serialiser = bindS code serialiser $ \c -> case c of
	'B' -> mapS (Builtin `IFun` unBuiltin) serialiser
	'P' -> mapS (Prim `IFun` unPrim) serialiser
	_   -> error $ "deserialise Builtin: no parse"
	where
	    code s = case s of
		Prim _	  -> 'P'
		Builtin _ -> 'B'

	    unBuiltin x = let Builtin a = x in a
	    unPrim    x = let Prim    a = x in a

instance Serialisable Interface where
    serialiser = mapS (IFun con des) serialiser
	where
	    con = uncurry $ uncurry $ uncurry $ uncurry $ uncurry Interface
	    des = ((((iVersion /\ iImportedModules) /\ iScope) /\ iSignature) /\ iImports) /\ iBuiltin

