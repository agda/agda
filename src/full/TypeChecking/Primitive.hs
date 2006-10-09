{-# OPTIONS -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances #-}

{-| Primitive functions, such as addition on builtin integers.
-}
module TypeChecking.Primitive where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Char

import Syntax.Position
import Syntax.Common
import Syntax.Internal
import Syntax.Literal
import Syntax.Concrete.Pretty ()
import Syntax.Abstract.Name
import qualified Syntax.Concrete.Name as C

import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Errors

import Utils.Monad
import Utils.Pretty (pretty)

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
primIO	    = getBuiltin builtinIO
primUnit    = getBuiltin builtinUnit

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
builtinIO      = "IO"
builtinUnit    = "UNIT"

builtinTypes :: [String]
builtinTypes =
    [ builtinInteger
    , builtinFloat
    , builtinChar
    , builtinString
    , builtinBool
    , builtinUnit
    ]

---------------------------------------------------------------------------
-- * Primitive functions
---------------------------------------------------------------------------

data PrimitiveImpl = PrimImpl Type PrimFun

-- Haskell type to Agda type

newtype Str = Str { unStr :: String }
    deriving (Eq, Ord)

class PrimType a where
    primType :: a -> TCM Type

instance (PrimType a, PrimType b) => PrimTerm (a -> b) where
    primTerm _ = unEl <$> (primType (undefined :: a) --> primType (undefined :: b))

instance PrimTerm a => PrimType a where
    primType _ = el $ primTerm (undefined :: a)

class	 PrimTerm a	  where primTerm :: a -> TCM Term
instance PrimTerm Integer where primTerm _ = primInteger
instance PrimTerm Bool	  where primTerm _ = primBool
instance PrimTerm Char	  where primTerm _ = primChar
instance PrimTerm Double  where primTerm _ = primFloat
instance PrimTerm Str	  where primTerm _ = primString
instance PrimTerm ()	  where primTerm _ = primUnit

instance PrimTerm a => PrimTerm [a] where
    primTerm _ = list (primTerm (undefined :: a))

instance PrimTerm a => PrimTerm (IO a) where
    primTerm _ = io (primTerm (undefined :: a))

-- From Agda term to Haskell value

class ToTerm a where
    toTerm :: TCM (a -> Term)

instance ToTerm Integer where toTerm = return $ Lit . LitInt noRange
instance ToTerm Double  where toTerm = return $ Lit . LitFloat noRange
instance ToTerm Char	where toTerm = return $ Lit . LitChar noRange
instance ToTerm Str	where toTerm = return $ Lit . LitString noRange . unStr

instance ToTerm Bool where
    toTerm = do
	true  <- primTrue
	false <- primFalse
	return $ \b -> if b then true else false

-- | @buildList A ts@ builds a list of type @List A@. Assumes that the terms
--   @ts@ all have type @A@.
buildList :: Term -> TCM ([Term] -> Term)
buildList a = do
    nil'  <- primNil
    cons' <- primCons
    let nil       = nil'  `apply` [Arg Hidden a]
	cons x xs = cons' `apply` [Arg Hidden a, Arg NotHidden x, Arg NotHidden xs]
    return $ foldr cons nil

instance (PrimTerm a, ToTerm a) => ToTerm [a] where
    toTerm = do
	a      <- primTerm (undefined :: a)
	mkList <- buildList a
	fromA  <- toTerm
	return $ mkList . map fromA

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
	LitFloat _ x -> Just x
	_	     -> Nothing

instance FromTerm Char where
    fromTerm = fromLiteral $ \l -> case l of
	LitChar _ c -> Just c
	_	    -> Nothing

instance FromTerm Str where
    fromTerm = fromLiteral $ \l -> case l of
	LitString _ s -> Just $ Str s
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

instance (ToTerm a, FromTerm a) => FromTerm [a] where
    fromTerm = do
	nil'  <- primNil
	cons' <- primCons
	nil   <- isCon nil'
	cons  <- isCon cons'
	toA   <- fromTerm
	fromA <- toTerm
	return $ mkList nil cons toA fromA
	where
	    isCon (Lam _ b) = isCon $ absBody b
	    isCon (Con c _) = return c
	    isCon v	    = do
		d <- prettyTCM v
		typeError $ GenericError $ "expected constructor in built-in binding to " ++ show d
				-- TODO: check this when binding the things

	    mkList nil cons toA fromA t = do
		t <- reduce t
		let arg = Arg (argHiding t)
		case unArg t of
		    Con c [_]
			| c == nil  -> return $ YesReduction []
		    Con c [a,x,xs]
			| c == cons ->
			    redBind (toA x)
				(\x' -> arg $ Con c [a,x',xs]) $ \y ->
			    redBind
				(mkList nil cons toA fromA xs)
				(\xs' -> arg $ Con c [a, Arg NotHidden $ fromA y, xs']) $ \ys ->
			    redReturn (y : ys)
		    _ -> return $ NoReduction t

-- | Conceptually: @redBind m f k = either (return . Left . f) k =<< m@
redBind :: TCM (Reduced a a') -> (a -> b) -> 
	     (a' -> TCM (Reduced b b')) -> TCM (Reduced b b')
redBind ma f k = do
    r <- ma
    case r of
	NoReduction x	-> return $ NoReduction $ f x
	YesReduction y	-> k y

redReturn :: a -> TCM (Reduced a' a)
redReturn = return . YesReduction

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
mkPrimFun1 :: (PrimType a, PrimType b, FromTerm a, ToTerm b) =>
	      (a -> b) -> TCM PrimitiveImpl
mkPrimFun1 f = do
    toA   <- fromTerm
    fromB <- toTerm
    t	  <- primType f
    return $ PrimImpl t $ PrimFun 1 $ \[v] ->
	redBind (toA v)
	    (\v' -> [v']) $ \x ->
	redReturn $ fromB $ f x

mkPrimFun2 :: (PrimType a, PrimType b, PrimType c, FromTerm a, ToTerm a, FromTerm b, ToTerm c) =>
	      (a -> b -> c) -> TCM PrimitiveImpl
mkPrimFun2 f = do
    toA   <- fromTerm
    fromA <- toTerm
    toB	  <- fromTerm
    fromC <- toTerm
    t	  <- primType f
    return $ PrimImpl t $ PrimFun 1 $ \[v,w] ->
	redBind (toA v)
	    (\v' -> [v',w]) $ \x ->
	redBind (toB w)
	    (\w' -> [Arg (argHiding v) (fromA x), w']) $ \y ->
	redReturn $ fromC $ f x y

-- Abstract primitive functions
abstractPrim :: PrimType a => a -> TCM PrimitiveImpl
abstractPrim x = abstractFromType (primType x)

abstractFromType :: TCM Type -> TCM PrimitiveImpl
abstractFromType mt = do
    t <- mt
    return $ PrimImpl t $ PrimFun (arity t) $ \args -> NoReduction <$> normalise args

-- Type combinators
infixr 4 -->

(-->) :: TCM Type -> TCM Type -> TCM Type
a --> b = do
    a' <- a
    b' <- b
    return $ El (getSort a' `sLub` getSort b') $ Fun (Arg NotHidden a') b'

gpi :: Hiding -> TCM Type -> TCM Type -> TCM Type
gpi h a b = do
    a' <- a
    x  <- freshName_ "x"
    b' <- addCtx x a' b
    return $ El (getSort a' `sLub` getSort b') $ Pi (Arg h a') (Abs "x" b')

hPi = gpi Hidden
nPi = gpi NotHidden

var :: Int -> TCM Term
var n = return $ Var n []

list :: TCM Term -> TCM Term
list t = do
    t'	 <- t
    list <- primList
    return $ list `apply` [Arg NotHidden t']

io :: TCM Term -> TCM Term
io t = do
    t' <- t
    io <- primIO
    return $ io `apply` [Arg NotHidden t']

el :: TCM Term -> TCM Type
el t = El (Type 0) <$> t

tset :: TCM Type
tset = return $ sort (Type 0)

---------------------------------------------------------------------------
-- * The actual primitive functions
---------------------------------------------------------------------------

type Op   a = a -> a -> a
type Fun  a = a -> a
type Rel  a = a -> a -> Bool
type Pred a = a -> Bool

primitiveFunctions :: Map String (TCM PrimitiveImpl)
primitiveFunctions = Map.fromList

    -- Integer functions
    [ "primIntegerPlus"	    |-> mkPrimFun2 ((+)	       :: Op Integer)
    , "primIntegerMinus"    |-> mkPrimFun2 ((-)	       :: Op Integer)
    , "primIntegerTimes"    |-> mkPrimFun2 ((*)	       :: Op Integer)
    , "primIntegerDiv"	    |-> mkPrimFun2 (div	       :: Op Integer)    -- partial
    , "primIntegerMod"	    |-> mkPrimFun2 (mod	       :: Op Integer)    -- partial
    , "primIntegerEquals"   |-> mkPrimFun2 ((==)       :: Rel Integer)
    , "primIntegerLess"	    |-> mkPrimFun2 ((<)	       :: Rel Integer)
    , "primShowInteger"	    |-> mkPrimFun1 (Str . show :: Integer -> Str)

    -- Floating point functions
    , "primIntegerToFloat"  |-> mkPrimFun1 (fromIntegral :: Integer -> Double)
    , "primFloatPlus"	    |-> mkPrimFun2 ((+)		 :: Op Double)
    , "primFloatMinus"	    |-> mkPrimFun2 ((-)		 :: Op Double)
    , "primFloatTimes"	    |-> mkPrimFun2 ((*)		 :: Op Double)
    , "primFloatDiv"	    |-> mkPrimFun2 ((/)		 :: Op Double)
    , "primFloatLess"	    |-> mkPrimFun2 ((<)		 :: Rel Double)
    , "primRound"	    |-> mkPrimFun1 (round	 :: Double -> Integer)
    , "primFloor"	    |-> mkPrimFun1 (floor	 :: Double -> Integer)
    , "primCeiling"	    |-> mkPrimFun1 (ceiling	 :: Double -> Integer)
    , "primExp"		    |-> mkPrimFun1 (exp		 :: Fun Double)
    , "primLog"		    |-> mkPrimFun1 (log		 :: Fun Double)    -- partial
    , "primSin"		    |-> mkPrimFun1 (sin		 :: Fun Double)
    , "primShowFloat"	    |-> mkPrimFun1 (Str . show	 :: Double -> Str)

    -- Character functions
    , "primIsLower"	    |-> mkPrimFun1 isLower
    , "primIsDigit"	    |-> mkPrimFun1 isDigit
    , "primIsAlpha"	    |-> mkPrimFun1 isAlpha
    , "primIsSpace"	    |-> mkPrimFun1 isSpace
    , "primIsAscii"	    |-> mkPrimFun1 isAscii
    , "primIsLatin1"	    |-> mkPrimFun1 isLatin1
    , "primIsPrint"	    |-> mkPrimFun1 isPrint
    , "primIsHexDigit"	    |-> mkPrimFun1 isHexDigit
    , "primToUpper"	    |-> mkPrimFun1 toUpper
    , "primToLower"	    |-> mkPrimFun1 toLower
    , "primCharToInteger"   |-> mkPrimFun1 (fromIntegral . fromEnum :: Char -> Integer)
    , "primIntegerToChar"   |-> mkPrimFun1 (toEnum . fromIntegral   :: Integer -> Char)
    , "primShowChar"	    |-> mkPrimFun1 (Str . show . pretty . LitChar noRange)

    -- String functions
    , "primStringToList"    |-> mkPrimFun1 unStr
    , "primStringFromList"  |-> mkPrimFun1 Str
    , "primStringAppend"    |-> mkPrimFun2 (\s1 s2 -> Str $ unStr s1 ++ unStr s2)
    , "primStringEqual"	    |-> mkPrimFun2 ((==) :: Rel Str)
    , "primShowString"	    |-> mkPrimFun1 (Str . show . pretty . LitString noRange . unStr)

    -- IO functions
    , "primPutStr"	    |-> abstractPrim (putStr . unStr)

				-- we can't build polymorphic types automatically
    , "primIOReturn"	    |-> abstractFromType (
				    hPi tset $ el (var 0) --> el (io $ var 0)
				)
    , "primIOBind"	    |-> abstractFromType (
				    hPi tset $ hPi tset $
				    el (io (var 1))
				    --> (el (var 1) --> el (io (var 0)))
				    --> el (io (var 0))
				)
    ]
    where
	(|->) = (,)

lookupPrimitiveFunction :: String -> TCM PrimitiveImpl
lookupPrimitiveFunction x =
    case Map.lookup x primitiveFunctions of
	Just p	-> p
	Nothing	-> typeError $ NoSuchPrimitiveFunction x

-- | Rebind a primitive. Assumes everything is type correct. Used when
--   importing a module with primitives.
rebindPrimitive :: String -> TCM PrimFun
rebindPrimitive x = do
    PrimImpl _ pf <- lookupPrimitiveFunction x
    bindPrimitive x pf
    return pf

