{-# OPTIONS -fglasgow-exts #-}

{-| Primitive functions, such as addition on builtin integers.
-}
module TypeChecking.Primitive where

import Data.Map (Map)
import qualified Data.Map as Map

import Syntax.Position
import Syntax.Common
import Syntax.Internal
import Syntax.Literal
import Syntax.Abstract.Name
import qualified Syntax.Concrete.Name as C

import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Reduce

import Utils.Monad

---------------------------------------------------------------------------
-- * The names of built-in things
---------------------------------------------------------------------------

primInteger = getBuiltin builtinInteger
primFloat   = getBuiltin builtinFloat
primChar    = getBuiltin builtinChar
primString  = getBuiltin builtinString
primBool    = getBuiltin builtinBool
primTrue    = getBuiltin builtinTrue
primFalse   = getBuiltin builtinFalse
primList    = getBuiltin builtinList
primNil	    = getBuiltin builtinNil
primCons    = getBuiltin builtinCons

builtinInteger = "INTEGER"
builtinFloat   = "FLOAT"
builtinChar    = "CHAR"
builtinString  = "STRING"
builtinBool    = "BOOL"
builtinTrue    = "TRUE"
builtinFalse   = "FALSE"
builtinList    = "LIST"
builtinNil     = "NIL"
builtinCons    = "CONS"

builtinTypes :: [String]
builtinTypes =
    [ builtinInteger
    , builtinFloat
    , builtinChar
    , builtinString
    , builtinBool
    ]

---------------------------------------------------------------------------
-- * Primitive functions
---------------------------------------------------------------------------

data PrimitiveImpl = PrimImpl Type PrimFun

-- Haskell type to Agda type

class PrimType a where
    primType :: a -> TCM Type

instance (PrimType a, PrimType b) => PrimType (a -> b) where
    primType _ = primType (undefined :: a) --> primType (undefined :: b)

instance PrimType Integer where
    primType _ = el primInteger

instance PrimType Bool where
    primType _ = el primBool

instance PrimType Char where
    primType _ = el primChar

instance PrimType Double where
    primType _ = el primFloat

instance PrimType String where
    primType _ = el primString

-- From Agda term to Haskell value

class ToTerm a where
    toTerm :: TCM (a -> Term)

instance ToTerm Integer where toTerm = return $ Lit . LitInt noRange
instance ToTerm Double  where toTerm = return $ Lit . LitFloat noRange
instance ToTerm Char	where toTerm = return $ Lit . LitChar noRange
instance ToTerm String	where toTerm = return $ Lit . LitString noRange

instance ToTerm Bool where
    toTerm = do
	true  <- primTrue
	false <- primFalse
	return $ \b -> if b then true else false

-- From Haskell value to Agda term

type FromTermFunction a = Arg Term -> TCM (Reduced (Arg Term) a)

class FromTerm a where
    fromTerm :: TCM (FromTermFunction a)

instance FromTerm Integer where
    fromTerm = fromLiteral $ \l -> case l of
	LitInt _ n -> Just n
	_	   -> Nothing

instance FromTerm Double where
    fromTerm = fromLiteral $ \l -> case l of
	LitFloat _ n -> Just n
	_	     -> Nothing

instance FromTerm Char where
    fromTerm = fromLiteral $ \l -> case l of
	LitChar _ n -> Just n
	_	    -> Nothing

instance FromTerm String where
    fromTerm = fromLiteral $ \l -> case l of
	LitString _ n -> Just n
	_	      -> Nothing

instance FromTerm Bool where
    fromTerm = do
	true  <- primTrue
	false <- primFalse
	fromReducedTerm $ \t -> case t of
	    _	| t === true  -> Just True
		| t === false -> Just False
		| otherwise   -> Nothing
	where
	    Def x [] === Def y []   = x == y
	    Con x [] === Con y []   = x == y
	    Var n [] === Var m []   = n == m
	    _	     === _	    = False

-- Currying

fromReducedTerm :: (Term -> Maybe a) -> TCM (FromTermFunction a)
fromReducedTerm f = return $ \t -> do
    t <- reduce t
    case f $ unArg t of
	Just x	-> return $ YesReduction x
	Nothing	-> return $ NoReduction t

fromLiteral :: (Literal -> Maybe a) -> TCM (FromTermFunction a)
fromLiteral f = fromReducedTerm $ \t -> case t of
    Lit lit -> f lit
    _	    -> Nothing

-- Tying the knot
primitiveFunction1 :: (PrimType a, PrimType b, FromTerm a, ToTerm b) =>
		     (a -> b) -> TCM PrimitiveImpl
primitiveFunction1 f = do
    toA   <- fromTerm
    fromB <- toTerm
    t	  <- primType f
    return $ PrimImpl t $ PrimFun 1 $ \[v] -> do
	r <- toA v
	case r of
	    NoReduction v'  -> return $ NoReduction [v']
	    YesReduction x  -> return $ YesReduction $ fromB $ f x

primitiveFunction2 :: (PrimType a, PrimType b, PrimType c, FromTerm a, ToTerm a, FromTerm b, ToTerm c) =>
		     (a -> b -> c) -> TCM PrimitiveImpl
primitiveFunction2 f = do
    toA   <- fromTerm
    fromA <- toTerm
    toB	  <- fromTerm
    fromC <- toTerm
    t	  <- primType f
    return $ PrimImpl t $ PrimFun 1 $ \[v,w] -> do
	r <- toA v
	case r of
	    NoReduction v'  -> return $ NoReduction [v', w]
	    YesReduction x  -> do
		r <- toB w
		case r of
		    NoReduction w'  -> return $ NoReduction [Arg (argHiding v) (fromA x), w']
		    YesReduction y  -> return $ YesReduction $ fromC $ f x y

infixr 4 -->

(-->) :: TCM Type -> TCM Type -> TCM Type
a --> b = do
    a' <- a
    b' <- b
    return $ Fun (Arg NotHidden a') b'

el :: TCM Term -> TCM Type
el t = flip El (Type 0) <$> t

---------------------------------------------------------------------------
-- * The actual primitive functions
---------------------------------------------------------------------------

primitiveFunctions :: Map String (TCM PrimitiveImpl)
primitiveFunctions = Map.fromList
    [ "integerPlus"   |-> primIntPlus
    , "integerMinus"  |-> primIntMinus
    , "integerEquals" |-> primIntEquals
    ]
    where
	(|->) = (,)

lookupPrimitiveFunction :: Name -> TCM PrimitiveImpl
lookupPrimitiveFunction x =
    case Map.lookup (nameString x) primitiveFunctions of
	Just p	-> p
	Nothing	-> typeError $ NoSuchPrimitiveFunction x
    where
	nameString (Name _ (C.Name _ s)) = s
	nameString (Name _ (C.NoName _)) = "_"

primIntPlus   = primitiveFunction2 ((+)  :: Integer -> Integer -> Integer)
primIntMinus  = primitiveFunction2 ((-)  :: Integer -> Integer -> Integer)
primIntEquals = primitiveFunction2 ((==) :: Integer -> Integer -> Bool)

