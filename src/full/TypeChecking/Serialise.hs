{-# OPTIONS -fallow-overlapping-instances #-}

module TypeChecking.Serialise where

import Control.Monad
import Data.Binary

import Syntax.Concrete.Name as C
import Syntax.Abstract.Name as A
import Syntax.Internal
import Syntax.Scope
import Syntax.Position
import Syntax.Common
import Syntax.Fixity
import Syntax.Literal

import TypeChecking.Monad

import Utils.Serialise
import Utils.Tuple

-- | Current version of the interface. Only interface files of this version
--   will be parsed.
currentInterfaceVersion :: InterfaceVersion
currentInterfaceVersion = InterfaceVersion 111

instance Binary InterfaceVersion where
    put (InterfaceVersion v) = put v
    get = do
	v <- liftM InterfaceVersion get
	if (v == currentInterfaceVersion)
	    then return v
	    else fail "Wrong interface version"

instance Binary ModuleName where
  put (MName a b) = put a >> put b
  get		  = liftM2 MName get get

-- instance Serialisable ModuleName where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry MName
-- 	    des = mnameId /\ mnameConcrete

instance Binary C.Name where
    put (C.Name r xs) = put r >> put xs
    get = liftM2 C.Name get get

-- instance Serialisable C.Name where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry C.Name
-- 	    des (C.Name r xs) = (r,xs)

instance Binary NamePart where
  put Hole = putWord8 0
  put (Id a) = putWord8 1 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return Hole
      1 -> get >>= \a -> return (Id a)
      _ -> fail "no parse"

-- instance Serialisable C.NamePart where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = maybe C.Hole C.Id
-- 	    des Hole   = Nothing
-- 	    des (Id s) = Just s

instance Binary Range where
    put _ = return ()
    get	  = return $ Range p p
	where p = Pn "[imported]" 0 0
--     put (Range a b) = put a >> put b
--     get = liftM2 Range get get

-- instance Serialisable Range where
--     serialiser = returnS $ Range p p -- mapS (IFun con des) serialiser
-- 	where
-- 	    p = Pn "<imported>" 0 0
-- 	    con = uncurry Range
-- 	    des = rStart /\ rEnd

instance Binary Position where
    put NoPos	   = putWord8 0
    put (Pn f l c) = putWord8 1 >> put f >> put l >> put c
    get = do
	tag_ <- getWord8
	case tag_ of
	    0	-> return NoPos
	    1	-> liftM3 Pn get get get
	    _ -> fail "no parse"

-- instance Serialisable Position where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = maybe NoPos (uncurry $ uncurry Pn)
-- 	    des NoPos	   = Nothing
-- 	    des (Pn f l c) = Just ((f,l),c)

instance Binary C.QName where
  put (Qual a b) = putWord8 0 >> put a >> put b
  put (C.QName a) = putWord8 1 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (Qual a b)
      1 -> get >>= \a -> return (C.QName a)
      _ -> fail "no parse"

-- instance Serialisable C.QName where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = either C.QName (uncurry C.Qual)
-- 	    des (C.QName x)  = Left x
-- 	    des (C.Qual m x) = Right (m,x)

instance Binary ModuleScope where
  put (ModuleScope a b c) = put a >> put b >> put c
  get = get >>= \a -> get >>= \b -> get >>= \c -> return (ModuleScope a b c)

-- instance Serialisable ModuleScope where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry $ uncurry ModuleScope
-- 	    des = (moduleArity /\ moduleAccess) /\ moduleContents

instance Binary Access where
  put PrivateAccess = putWord8 0
  put PublicAccess = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return PrivateAccess
      1 -> return PublicAccess
      _ -> fail "no parse"

-- instance Serialisable Access where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con True  = PublicAccess
-- 	    con False = PrivateAccess
-- 	    des PublicAccess  = True
-- 	    des PrivateAccess = False

instance Binary NameSpace where
  put (NSpace a b c) = put a >> put b >> put c
  get = get >>= \a -> get >>= \b -> get >>= \c -> return (NSpace a b c)

-- instance Serialisable NameSpace where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry $ uncurry NSpace
-- 	    des = (moduleName /\ definedNames ) /\ modules

instance Binary DefinedName where
  put (DefinedName a b c d) = put a >> put b >> put c >> put d
  get = get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> return (DefinedName a b c d)

-- instance Serialisable DefinedName where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry $ uncurry $ uncurry DefinedName 
-- 	    des = ((access /\ kindOfName) /\ fixity) /\ theName

instance Binary KindOfName where
  put FunName = putWord8 0
  put ConName = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return FunName
      1 -> return ConName
      _ -> fail "no parse"

-- instance Serialisable KindOfName where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con True  = FunName
-- 	    con False = ConName
-- 	    des FunName = True
-- 	    des ConName = False

instance Binary Syntax.Fixity.Fixity where
  put (LeftAssoc a b) = putWord8 0 >> put a >> put b
  put (RightAssoc a b) = putWord8 1 >> put a >> put b
  put (NonAssoc a b) = putWord8 2 >> put a >> put b
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (LeftAssoc a b)
      1 -> get >>= \a -> get >>= \b -> return (RightAssoc a b)
      2 -> get >>= \a -> get >>= \b -> return (NonAssoc a b)
      _ -> fail "no parse"

-- instance Serialisable Fixity where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con ('l',r,n) = LeftAssoc r n
-- 	    con ('r',r,n) = RightAssoc r n
-- 	    con ('n',r,n) = NonAssoc r n
-- 	    con _	    = error $ "deserialise Fixity: no parse"
-- 	    des (LeftAssoc  r n) = ('l',r,n)
-- 	    des (RightAssoc r n) = ('r',r,n)
-- 	    des (NonAssoc   r n) = ('n',r,n)

instance Binary A.QName where
  put (A.QName a b c) = put a >> put b >> put c
  get = get >>= \a -> get >>= \b -> get >>= \c -> return (A.QName a b c)

-- instance Serialisable A.QName where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry $ uncurry A.QName
-- 	    des = (qnameName /\ qnameModule) /\ qnameConcrete

instance Binary A.Name where
  put (A.Name a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (A.Name a b)

-- instance Serialisable A.Name where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry A.Name
-- 	    des = nameId /\ nameConcrete

instance Binary A.NameId where
  put (NameId a) = put a
  get = get >>= \a -> return (NameId a)

-- instance Serialisable NameId where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = NameId
-- 	    des (NameId n) = n

instance Binary ModuleDef where
  put (ModuleDef a b c d) = put a >> put b >> put c >> put d
  get = get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> return (ModuleDef a b c d)

-- instance Serialisable ModuleDef where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry $ uncurry $ uncurry ModuleDef
-- 	    des = ((mdefName /\ mdefTelescope) /\ mdefNofParams) /\ mdefDefs

instance (Binary a) => Binary (Syntax.Common.Arg a) where
  put (Arg a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Arg a b)

-- instance Serialisable a => Serialisable (Arg a) where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry Arg
-- 	    des = argHiding /\ unArg

instance Binary Syntax.Common.Hiding where
  put Hidden = putWord8 0
  put NotHidden = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return Hidden
      1 -> return NotHidden
      _ -> fail "no parse"

-- instance Serialisable Hiding where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con True	  = Hidden
-- 	    con False	  = NotHidden
-- 	    des Hidden	  = True
-- 	    des NotHidden = False

instance Binary Syntax.Internal.Type where
  put (El a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (El a b)

-- instance Serialisable Type where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con (s,t) = El s t
-- 	    des (El s t) = (s,t)

instance Binary Syntax.Internal.MetaId where
  put (MetaId a) = put a
  get = get >>= \a -> return (MetaId a)

-- instance Serialisable MetaId where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = MetaId 
-- 	    des (MetaId n) = n

instance (Binary a) => Binary (Syntax.Internal.Blocked a) where
  put (Blocked a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Blocked a b)

-- instance Serialisable a => Serialisable (Blocked a) where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry Blocked
-- 	    des = blockingMeta /\ blockee

instance (Binary a) => Binary (Syntax.Internal.Abs a) where
  put (Abs a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Abs a b)

-- instance Serialisable a => Serialisable (Abs a) where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry Abs
-- 	    des = absName /\ absBody

instance Binary Syntax.Internal.Term where
  put (Var a b) = putWord8 0 >> put a >> put b
  put (Lam a b) = putWord8 1 >> put a >> put b
  put (Lit a) = putWord8 2 >> put a
  put (Def a b) = putWord8 3 >> put a >> put b
  put (Con a b) = putWord8 4 >> put a >> put b
  put (Pi a b) = putWord8 5 >> put a >> put b
  put (Fun a b) = putWord8 6 >> put a >> put b
  put (Sort a) = putWord8 7 >> put a
  put (MetaV a b) = putWord8 8 >> put a >> put b
  put (BlockedV a) = putWord8 9 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (Var a b)
      1 -> get >>= \a -> get >>= \b -> return (Lam a b)
      2 -> get >>= \a -> return (Lit a)
      3 -> get >>= \a -> get >>= \b -> return (Def a b)
      4 -> get >>= \a -> get >>= \b -> return (Con a b)
      5 -> get >>= \a -> get >>= \b -> return (Pi a b)
      6 -> get >>= \a -> get >>= \b -> return (Fun a b)
      7 -> get >>= \a -> return (Sort a)
      8 -> get >>= \a -> get >>= \b -> return (MetaV a b)
      9 -> get >>= \a -> return (BlockedV a)
      _ -> fail "no parse"

-- instance Serialisable Term where
--     serialiser = bindS code serialiser $ \c -> case c of
-- 	    'V' -> mapS (uncurry Var `IFun` unVar) serialiser
-- 	    'L' -> mapS (uncurry Lam `IFun` unLam) serialiser
-- 	    'I' -> mapS (Lit `IFun` unLit) serialiser
-- 	    'D' -> mapS (uncurry Def `IFun` unDef) serialiser
-- 	    'C' -> mapS (uncurry Con `IFun` unCon) serialiser
-- 	    'P' -> mapS (uncurry Pi `IFun` unPi) serialiser
-- 	    'F' -> mapS (uncurry Fun `IFun` unFun) serialiser
-- 	    'S' -> mapS (Sort `IFun` unSort) serialiser
-- 	    'B' -> mapS (BlockedV `IFun` unBlockedV) serialiser
-- 	    'M' -> mapS (uncurry MetaV `IFun` unMetaV) serialiser
-- 	    _	-> error $ "deserialise Term: no parse"
-- 	where
-- 	    code t = case t of
-- 		Var _ _    -> 'V'
-- 		Lam  _ _   -> 'L'
-- 		Lit _	   -> 'I'
-- 		Def _ _    -> 'D'
-- 		Con _ _    -> 'C'
-- 		Pi _ _	   -> 'P'
-- 		Fun _ _    -> 'F'
-- 		Sort _	   -> 'S'
-- 		MetaV _ _  -> 'M'
-- 		BlockedV _ -> 'B'

-- 	    unVar      x = let Var	a b = x in (a,b)
-- 	    unLam      x = let Lam	a b = x in (a,b)
-- 	    unDef      x = let Def	a b = x in (a,b)
-- 	    unCon      x = let Con	a b = x in (a,b)
-- 	    unLit      x = let Lit	a   = x in a
-- 	    unPi       x = let Pi	a b = x in (a,b)
-- 	    unFun      x = let Fun	a b = x in (a,b)
-- 	    unSort     x = let Sort	a   = x in a
-- 	    unMetaV    x = let MetaV	a b = x in (a,b)
-- 	    unBlockedV x = let BlockedV a   = x in a

instance Binary Syntax.Internal.Sort where
  put (Type a) = putWord8 0 >> put a
  put Prop = putWord8 1
  put (Lub a b) = putWord8 2 >> put a >> put b
  put (Suc a) = putWord8 3 >> put a
  put (MetaS a) = putWord8 4 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> return (Type a)
      1 -> return Prop
      2 -> get >>= \a -> get >>= \b -> return (Lub a b)
      3 -> get >>= \a -> return (Suc a)
      4 -> get >>= \a -> return (MetaS a)
      _ -> fail "no parse"

-- instance Serialisable Sort where
--     serialiser = bindS code serialiser $ \c -> case c of
-- 	    'T' -> mapS (Type `IFun` unType) serialiser
-- 	    'P' -> returnS Prop
-- 	    'L' -> mapS (uncurry Lub `IFun` unLub) serialiser
-- 	    'S' -> mapS (Suc `IFun` unSuc) serialiser
-- 	    'M' -> mapS (MetaS `IFun` unMetaS) serialiser
-- 	    _	-> error $ "deserialise Sort: no parse"
-- 	where
-- 	    code s = case s of
-- 		Type _	-> 'T'
-- 		Prop	-> 'P'
-- 		Lub _ _ -> 'L'
-- 		Suc _	-> 'S'
-- 		MetaS _ -> 'M'

-- 	    unType  x = let Type  a   = x in a
-- 	    unSuc   x = let Suc   a   = x in a
-- 	    unLub   x = let Lub   a b = x in (a,b)
-- 	    unMetaS x = let MetaS a   = x in a

instance Binary Syntax.Literal.Literal where
  put (LitInt a b) = putWord8 0 >> put a >> put b
  put (LitFloat a b) = putWord8 1 >> put a >> put b
  put (LitString a b) = putWord8 2 >> put a >> put b
  put (LitChar a b) = putWord8 3 >> put a >> put b
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (LitInt a b)
      1 -> get >>= \a -> get >>= \b -> return (LitFloat a b)
      2 -> get >>= \a -> get >>= \b -> return (LitString a b)
      3 -> get >>= \a -> get >>= \b -> return (LitChar a b)
      _ -> fail "no parse"

-- instance Serialisable Literal where
--     serialiser = bindS code serialiser $ \c -> case c of
-- 	    'n' -> mapS (uncurry LitInt `IFun` unInt) serialiser
-- 	    'f' -> mapS (uncurry LitFloat `IFun` unFloat) serialiser
-- 	    's' -> mapS (uncurry LitString `IFun` unString) serialiser
-- 	    'c' -> mapS (uncurry LitChar `IFun` unChar) serialiser
-- 	    _	-> error $ "deserialise Literal: no parse"
-- 	where
-- 	    code s = case s of
-- 		LitInt _ _    -> 'n'
-- 		LitFloat _ _  -> 'f'
-- 		LitString _ _ -> 's'
-- 		LitChar _ _   -> 'c'

-- 	    unInt    x = let LitInt    a b = x in (a,b)
-- 	    unFloat  x = let LitFloat  a b = x in (a,b)
-- 	    unString x = let LitString a b = x in (a,b)
-- 	    unChar   x = let LitChar   a b = x in (a,b)

-- instance Serialisable Integer where
--     serialiser = mapS (IFun read show) serialiser

-- instance Serialisable Double where
--     serialiser = mapS (IFun read show) serialiser

instance Binary Definition where
  put (Defn a b c) = put a >> put b >> put c
  get = get >>= \a -> get >>= \b -> get >>= \c -> return (Defn a b c)

-- instance Serialisable Definition where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry $ uncurry Defn
-- 	    des = (defType /\ defFreeVars ) /\ theDef

instance Binary Defn where
  put Axiom = putWord8 0
  put (Function a b) = putWord8 1 >> put a >> put b
  put (Datatype a b c d e) = putWord8 2 >> put a >> put b >> put c >> put d >> put e
  put (Constructor a b c) = putWord8 3 >> put a >> put b >> put c
  put (Primitive a b c) = putWord8 4 >> put a >> put b >> put c
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return Axiom
      1 -> get >>= \a -> get >>= \b -> return (Function a b)
      2 -> get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> get >>= \e -> return (Datatype a b c d e)
      3 -> get >>= \a -> get >>= \b -> get >>= \c -> return (Constructor a b c)
      4 -> get >>= \a -> get >>= \b -> get >>= \c -> return (Primitive a b c)
      _ -> fail "no parse"

-- instance Serialisable Defn where
--     serialiser = bindS code serialiser $ \c -> case c of
-- 	    'A' -> returnS Axiom
-- 	    'F' -> mapS (uncurry Function `IFun` unFunction) serialiser
-- 	    'D' -> mapS (datatype `IFun` unData) serialiser
-- 	    'C' -> mapS (cons `IFun` unCons) serialiser
-- 	    'P' -> mapS (prim `IFun` unPrim) serialiser
-- 	    _	-> error $ "deserialise Defn: no parse"
-- 	where
-- 	    code s = case s of
-- 		Axiom		   -> 'A'
-- 		Function _ _	   -> 'F'
-- 		Datatype _ _ _ _ _ -> 'D'
-- 		Constructor _ _ _  -> 'C'
-- 		Primitive _ _ _    -> 'P'

-- 	    datatype ((a,b),(c,(d,e))) = Datatype a b c d e
-- 	    cons (a,b,c)	       = Constructor a b c
-- 	    prim (a,b,c)	       = Primitive a b c

-- 	    unFunction x = let Function    a b	     = x in (a,b)
-- 	    unData     x = let Datatype    a b c d e = x in ((a,b),(c,(d,e)))
-- 	    unCons     x = let Constructor a b c     = x in (a,b,c)
-- 	    unPrim     x = let Primitive   a b c     = x in (a,b,c)

instance Binary Syntax.Common.IsAbstract where
  put AbstractDef = putWord8 0
  put ConcreteDef = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return AbstractDef
      1 -> return ConcreteDef
      _ -> fail "no parse"

-- instance Serialisable IsAbstract where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con True	      = AbstractDef
-- 	    con False	      = ConcreteDef
-- 	    des AbstractDef = True
-- 	    des ConcreteDef = False

instance Binary Syntax.Internal.Clause where
  put (Clause a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Clause a b)

-- instance Serialisable Clause where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry Clause
-- 	    des (Clause ps b) = (ps,b)

instance Binary Syntax.Internal.ClauseBody where
  put (Body a) = putWord8 0 >> put a
  put (Bind a) = putWord8 1 >> put a
  put (NoBind a) = putWord8 2 >> put a
  put NoBody = putWord8 3
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> return (Body a)
      1 -> get >>= \a -> return (Bind a)
      2 -> get >>= \a -> return (NoBind a)
      3 -> return NoBody
      _ -> fail "no parse"

-- instance Serialisable ClauseBody where
--     serialiser = bindS code serialiser $ \c -> case c of
-- 	    'b' -> mapS (Bind `IFun` unBind) serialiser
-- 	    'n' -> mapS (NoBind `IFun` unNoBind) serialiser
-- 	    'o' -> mapS (Body `IFun` unBody) serialiser
-- 	    '-' -> returnS NoBody
-- 	    _	-> error $ "deserialise ClauseBody: no parse"
-- 	where
-- 	    code s = case s of
-- 		Bind _	 -> 'b'
-- 		NoBind _ -> 'n'
-- 		Body _	 -> 'o'
-- 		NoBody	 -> '-'

-- 	    unBind   x = let Bind   a = x in a
-- 	    unNoBind x = let NoBind a = x in a
-- 	    unBody   x = let Body   a = x in a

instance Binary Syntax.Internal.Pattern where
  put (VarP a) = putWord8 0 >> put a
  put (ConP a b) = putWord8 1 >> put a >> put b
  put (LitP a) = putWord8 2 >> put a
  put WildP = putWord8 3
  put AbsurdP = putWord8 4
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> return (VarP a)
      1 -> get >>= \a -> get >>= \b -> return (ConP a b)
      2 -> get >>= \a -> return (LitP a)
      3 -> return WildP
      4 -> return AbsurdP
      _ -> fail "no parse"

-- instance Serialisable Pattern where
--     serialiser = bindS code serialiser $ \c -> case c of
-- 	    'v' -> mapS (VarP `IFun` unVarP) serialiser
-- 	    'c' -> mapS (uncurry ConP `IFun` unConP) serialiser
-- 	    'l' -> mapS (LitP `IFun` unLitP) serialiser
-- 	    '-' -> returnS AbsurdP
-- 	    '_' -> returnS WildP
-- 	    _	-> error $ "deserialise Pattern: no parse"
-- 	where
-- 	    code s = case s of
-- 		VarP _	 -> 'v'
-- 		ConP _ _ -> 'c'
-- 		LitP _	 -> 'l'
-- 		WildP	 -> '_'
-- 		AbsurdP  -> '-'

-- 	    unVarP x = let VarP a   = x in a
-- 	    unLitP x = let LitP a   = x in a
-- 	    unConP x = let ConP a b = x in (a,b)

instance Binary a => Binary (Builtin a) where
    put (Prim a) = putWord8 0 >> put a
    put (Builtin a) = putWord8 1 >> put a
    get = do
	tag_ <- getWord8
	case tag_ of
	    0	-> liftM Prim get
	    1	-> liftM Builtin get
	    _ -> fail "no parse"

-- instance Serialisable a => Serialisable (Builtin a) where
--     serialiser = bindS code serialiser $ \c -> case c of
-- 	'B' -> mapS (Builtin `IFun` unBuiltin) serialiser
-- 	'P' -> mapS (Prim `IFun` unPrim) serialiser
-- 	_   -> error $ "deserialise Builtin: no parse"
-- 	where
-- 	    code s = case s of
-- 		Prim _	  -> 'P'
-- 		Builtin _ -> 'B'

-- 	    unBuiltin x = let Builtin a = x in a
-- 	    unPrim    x = let Prim    a = x in a

instance Binary Interface where
    put (Interface a b c d e f) = put a >> put b >> put c >> put d >> put e >> put f
    get = liftM5 Interface get get get get get `ap` get

-- instance Serialisable Interface where
--     serialiser = mapS (IFun con des) serialiser
-- 	where
-- 	    con = uncurry $ uncurry $ uncurry $ uncurry $ uncurry Interface
-- 	    des = ((((iVersion /\ iImportedModules) /\ iScope) /\ iSignature) /\ iImports) /\ iBuiltin

