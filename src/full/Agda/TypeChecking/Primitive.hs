{-# LANGUAGE CPP, FlexibleInstances, UndecidableInstances,
             GeneralizedNewtypeDeriving, ScopedTypeVariables
  #-}

{-| Primitive functions, such as addition on builtin integers.
-}
module Agda.TypeChecking.Primitive where

import Control.Monad
import Control.Monad.Error
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Char

import Agda.Interaction.Options

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Quote (quoteType, quotingKit)
import Agda.TypeChecking.Pretty ()  -- instances only
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Level

import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Rewrite a literal to constructor form if possible.
constructorForm :: Term -> TCM Term
constructorForm v = case ignoreSharing v of
{- 2012-04-02 changed semantics of DontCare
-- Andreas, 2011-10-03, the following line restores IrrelevantLevel
    DontCare v                  -> constructorForm v
-}
    Lit (LitInt r n)            -> cons primZero primSuc (Lit . LitInt r) n
--     Level (Max [])              -> primLevelZero
--     Level (Max [ClosedLevel n]) -> cons primLevelZero primLevelSuc (Level . Max . (:[]) . ClosedLevel) n
    _                           -> return v
  where
    cons pZero pSuc lit n
      | n == 0  = pZero
      | n > 0   = do
        s <- pSuc
        return $ s `apply` [defaultArg $ lit $ n - 1]
      | otherwise	= return v

---------------------------------------------------------------------------
-- * Primitive functions
---------------------------------------------------------------------------

data PrimitiveImpl = PrimImpl Type PrimFun

-- Haskell type to Agda type

newtype Str = Str { unStr :: String }
    deriving (Eq, Ord)

newtype Nat = Nat { unNat :: Integer }
    deriving (Eq, Ord, Num, Integral, Enum, Real)

newtype Lvl = Lvl { unLvl :: Integer }
  deriving (Eq, Ord)

instance Show Lvl where
  show = show . unLvl

instance Show Nat where
    show = show . unNat

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
instance PrimTerm Nat	  where primTerm _ = primNat
instance PrimTerm Lvl     where primTerm _ = primLevel
instance PrimTerm QName   where primTerm _ = primQName
instance PrimTerm Type    where primTerm _ = primAgdaType

instance PrimTerm a => PrimTerm [a] where
    primTerm _ = list (primTerm (undefined :: a))

instance PrimTerm a => PrimTerm (IO a) where
    primTerm _ = io (primTerm (undefined :: a))

-- From Agda term to Haskell value

class ToTerm a where
    toTerm :: TCM (a -> Term)

instance ToTerm Integer where toTerm = return $ Lit . LitInt noRange
instance ToTerm Nat	where toTerm = return $ Lit . LitInt noRange . unNat
instance ToTerm Lvl	where toTerm = return $ Level . Max . (:[]) . ClosedLevel . unLvl
instance ToTerm Double  where toTerm = return $ Lit . LitFloat noRange
instance ToTerm Char	where toTerm = return $ Lit . LitChar noRange
instance ToTerm Str	where toTerm = return $ Lit . LitString noRange . unStr
instance ToTerm QName	where toTerm = return $ Lit . LitQName noRange

instance ToTerm Bool where
    toTerm = do
	true  <- primTrue
	false <- primFalse
	return $ \b -> if b then true else false

instance ToTerm Type where
    toTerm = snd <$> quotingKit

-- | @buildList A ts@ builds a list of type @List A@. Assumes that the terms
--   @ts@ all have type @A@.
buildList :: TCM ([Term] -> Term)
buildList = do
    nil'  <- primNil
    cons' <- primCons
    let nil       = nil'
	cons x xs = cons' `apply` [defaultArg x, defaultArg xs]
    return $ foldr cons nil

instance (PrimTerm a, ToTerm a) => ToTerm [a] where
    toTerm = do
	mkList <- buildList
	fromA  <- toTerm
	return $ mkList . map fromA

-- From Haskell value to Agda term

type FromTermFunction a = I.Arg Term -> TCM (Reduced (MaybeReduced (I.Arg Term)) a)

class FromTerm a where
    fromTerm :: TCM (FromTermFunction a)

instance FromTerm Integer where
    fromTerm = fromLiteral $ \l -> case l of
	LitInt _ n -> Just n
	_	   -> Nothing

instance FromTerm Nat where
    fromTerm = fromLiteral $ \l -> case l of
	LitInt _ n -> Just $ Nat n
	_	   -> Nothing

instance FromTerm Lvl where
    fromTerm = fromReducedTerm $ \l -> case l of
	Level (Max [ClosedLevel n]) -> Just $ Lvl n
	_                           -> Nothing

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

instance FromTerm QName where
    fromTerm = fromLiteral $ \l -> case l of
	LitQName _ x -> Just x
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
      isCon (Lam _ b)  = isCon $ absBody b
      isCon (Con c _)  = return c
      isCon (Shared p) = isCon (derefPtr p)
      isCon v          = do
        d <- prettyTCM v
        typeError $ GenericError $ "expected constructor in built-in binding to " ++ show d
                        -- TODO: check this when binding the things

      mkList nil cons toA fromA t = do
        b <- reduceB t
        let t = ignoreBlocking b
        let arg = Arg (ArgInfo { argInfoHiding = getHiding t
                               , argInfoRelevance = getRelevance t
                               , argInfoColors = argColors t
                               })
        case unArg t of
          Con c []
            | c == nil  -> return $ YesReduction []
          Con c [x,xs]
            | c == cons ->
              redBind (toA x)
                  (\x' -> notReduced $ arg $ Con c [ignoreReduced x',xs]) $ \y ->
              redBind
                  (mkList nil cons toA fromA xs)
                  (fmap $ \xs' -> arg $ Con c [defaultArg $ fromA y, xs']) $ \ys ->
              redReturn (y : ys)
          _ -> return $ NoReduction (reduced b)

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
    b <- reduceB t
    case f $ ignoreSharing $ unArg (ignoreBlocking b) of
	Just x	-> return $ YesReduction x
	Nothing	-> return $ NoReduction (reduced b)

fromLiteral :: (Literal -> Maybe a) -> TCM (FromTermFunction a)
fromLiteral f = fromReducedTerm $ \t -> case t of
    Lit lit -> f lit
    _	    -> Nothing

-- trustMe : {a : Level} {A : Set a} {x y : A} -> x ≡ y
primTrustMe :: TCM PrimitiveImpl
primTrustMe = do
  clo <- commandLineOptions
  when (optSafe clo) (typeError SafeFlagPrimTrustMe)
  t    <- hPi "a" (el primLevel) $
          hPi "A" (return $ sort $ varSort 0) $
          hPi "x" (El (varSort 1) <$> varM 0) $
          hPi "y" (El (varSort 2) <$> varM 1) $
          El (varSort 3) <$>
            primEquality <#> varM 3 <#> varM 2 <@> varM 1 <@> varM 0
  Con rf [] <- ignoreSharing <$> primRefl
  n         <- conPars . theDef <$> getConstInfo rf
  let refl x | n == 2    = Con rf [setRelevance Forced $ hide $ defaultArg x]
             | n == 3    = Con rf []
             | otherwise = __IMPOSSIBLE__
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 4 $ \ts ->
      case ts of
        [a, t, x, y] -> liftTCM $ do
              noConstraints $
                equalTerm (El (Type $ lvlView $ unArg a) (unArg t))
                          (unArg x) (unArg y)
              redReturn (refl $ unArg x)
            `catchError` \_ -> return (NoReduction $ map notReduced [a, t, x, y])
        _ -> __IMPOSSIBLE__

primQNameType :: TCM PrimitiveImpl
primQNameType = mkPrimFun1TCM (el primQName --> el primAgdaType) typeOfConst

primQNameDefinition :: TCM PrimitiveImpl
primQNameDefinition = do
  let argQName qn = [defaultArg (Lit (LitQName noRange qn))]
      app mt xs = do t <- mt
                     return $ apply t xs

      con qn Function{}    = app primAgdaDefinitionFunDef    (argQName qn)
      con qn Datatype{}    = app primAgdaDefinitionDataDef   (argQName qn)
      con qn Record{}      = app primAgdaDefinitionRecordDef (argQName qn)
      con _  Axiom{}       = app primAgdaDefinitionPostulate []
      con _  Primitive{}   = app primAgdaDefinitionPrimitive []
      con _  Constructor{} = app primAgdaDefinitionDataConstructor []

  unquoteQName <- fromTerm
  t <- el primQName --> el primAgdaDefinition
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ts ->
    case ts of
      [v] -> liftTCM $
        redBind (unquoteQName v)
            (\v' -> [v']) $ \x ->
        redReturn =<< con x . theDef =<< getConstInfo x
      _ -> __IMPOSSIBLE__

primDataConstructors :: TCM PrimitiveImpl
primDataConstructors = mkPrimFun1TCM (el primAgdaDataDef --> el (list primQName))
                                     (fmap (dataCons . theDef) . getConstInfo)

mkPrimLevelZero :: TCM PrimitiveImpl
mkPrimLevelZero = do
  t <- primType (undefined :: Lvl)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 0 $ \_ -> redReturn $ Level $ Max []

mkPrimLevelSuc :: TCM PrimitiveImpl
mkPrimLevelSuc = do
  t <- primType (id :: Lvl -> Lvl)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ ~[a] -> liftTCM $ do
    l <- levelView $ unArg a
    redReturn $ Level $ levelSuc l

mkPrimLevelMax :: TCM PrimitiveImpl
mkPrimLevelMax = do
  t <- primType (max :: Op Lvl)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 2 $ \ ~[a, b] -> liftTCM $ do
    Max as <- levelView $ unArg a
    Max bs <- levelView $ unArg b
    redReturn $ Level $ levelMax $ as ++ bs

mkPrimFun1TCM :: (FromTerm a, ToTerm b) => TCM Type -> (a -> TCM b) -> TCM PrimitiveImpl
mkPrimFun1TCM mt f = do
    toA   <- fromTerm
    fromB <- toTerm
    t     <- mt
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ts ->
      case ts of
        [v] -> liftTCM $
          redBind (toA v)
              (\v' -> [v']) $ \x ->
          redReturn . fromB =<< f x
        _ -> __IMPOSSIBLE__

-- Tying the knot
mkPrimFun1 :: (PrimType a, PrimType b, FromTerm a, ToTerm b) =>
	      (a -> b) -> TCM PrimitiveImpl
mkPrimFun1 f = do
    toA   <- fromTerm
    fromB <- toTerm
    t	  <- primType f
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 1 $ \ts ->
      case ts of
        [v] -> liftTCM $
          redBind (toA v)
              (\v' -> [v']) $ \x ->
          redReturn $ fromB $ f x
        _ -> __IMPOSSIBLE__

mkPrimFun2 :: (PrimType a, PrimType b, PrimType c, FromTerm a, ToTerm a, FromTerm b, ToTerm c) =>
	      (a -> b -> c) -> TCM PrimitiveImpl
mkPrimFun2 f = do
    toA   <- fromTerm
    fromA <- toTerm
    toB	  <- fromTerm
    fromC <- toTerm
    t	  <- primType f
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 2 $ \ts ->
      case ts of
        [v,w] -> liftTCM $
          redBind (toA v)
              (\v' -> [v', notReduced w]) $ \x ->
          redBind (toB w)
              (\w' -> [ reduced $ notBlocked $ Arg (argInfo v) (fromA x)
                      , w']) $ \y ->
          redReturn $ fromC $ f x y
        _ -> __IMPOSSIBLE__

mkPrimFun4 :: ( PrimType a, FromTerm a, ToTerm a
              , PrimType b, FromTerm b, ToTerm b
              , PrimType c, FromTerm c, ToTerm c
              , PrimType d, FromTerm d
              , PrimType e, ToTerm e) =>
	      (a -> b -> c -> d -> e) -> TCM PrimitiveImpl
mkPrimFun4 f = do
    (toA, fromA) <- (,) <$> fromTerm <*> toTerm
    (toB, fromB) <- (,) <$> fromTerm <*> toTerm
    (toC, fromC) <- (,) <$> fromTerm <*> toTerm
    toD          <- fromTerm
    fromE        <- toTerm
    t <- primType f
    return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 4 $ \ts ->
      let argFrom fromX a x =
            reduced $ notBlocked $ Arg (argInfo a) (fromX x)
      in case ts of
        [a,b,c,d] -> liftTCM $
          redBind (toA a)
              (\a' -> a' : map notReduced [b,c,d]) $ \x ->
          redBind (toB b)
              (\b' -> [argFrom fromA a x, b', notReduced c, notReduced d]) $ \y ->
          redBind (toC c)
              (\c' -> [ argFrom fromA a x
                      , argFrom fromB b y
                      , c', notReduced d]) $ \z ->
          redBind (toD d)
              (\d' -> [ argFrom fromA a x
                      , argFrom fromB b y
                      , argFrom fromC c z
                      , d']) $ \w ->

          redReturn $ fromE $ f x y z w
        _ -> __IMPOSSIBLE__

-- Type combinators
infixr 4 -->

(-->) :: TCM Type -> TCM Type -> TCM Type
a --> b = do
    a' <- a
    b' <- b
    return $ El (getSort a' `sLub` getSort b') $ Pi (Dom defaultArgInfo a') (NoAbs "_" b')

infixr 4 .-->

(.-->) :: TCM Type -> TCM Type -> TCM Type
a .--> b = do
    a' <- a
    b' <- b
    return $ El (getSort a' `sLub` getSort b') $
             Pi (Dom (setRelevance Irrelevant defaultArgInfo) a') (NoAbs "_" b')

gpi :: I.ArgInfo -> String -> TCM Type -> TCM Type -> TCM Type
gpi info name a b = do
  a <- a
  x <- freshName_ name
  b <- addCtx x (Dom info a) b
  return $ El (getSort a `dLub` Abs name (getSort b))
              (Pi (Dom info a) (Abs name b))

hPi, nPi :: String -> TCM Type -> TCM Type -> TCM Type
hPi = gpi $ setHiding Hidden $ defaultArgInfo
nPi = gpi defaultArgInfo

varM :: Int -> TCM Term
varM = return . var

infixl 9 <@>, <#>

gApply :: Hiding -> TCM Term -> TCM Term -> TCM Term
gApply h a b = do
    x <- a
    y <- b
    return $ x `apply` [Arg (setHiding h defaultArgInfo) y]

(<@>),(<#>) :: TCM Term -> TCM Term -> TCM Term
(<@>) = gApply NotHidden
(<#>) = gApply Hidden

list :: TCM Term -> TCM Term
list t = primList <@> t

io :: TCM Term -> TCM Term
io t = primIO <@> t

el :: TCM Term -> TCM Type
el t = El (mkType 0) <$> t

tset :: TCM Type
tset = return $ sort (mkType 0)

-- | Abbreviation: @argN = 'Arg' 'defaultArgInfo'@.

argN = Arg defaultArgInfo
domN = Dom defaultArgInfo

-- | Abbreviation: @argH = 'hide' 'Arg' 'defaultArgInfo'@.

argH = Arg $ setHiding Hidden defaultArgInfo
domH = Dom $ setHiding Hidden defaultArgInfo

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
    , "primIntegerEquality" |-> mkPrimFun2 ((==)       :: Rel Integer)
    , "primIntegerLess"	    |-> mkPrimFun2 ((<)	       :: Rel Integer)
    , "primIntegerAbs"      |-> mkPrimFun1 (Nat . abs  :: Integer -> Nat)
    , "primNatToInteger"    |-> mkPrimFun1 (unNat      :: Nat -> Integer)
    , "primShowInteger"	    |-> mkPrimFun1 (Str . show :: Integer -> Str)

    -- Natural number functions
    , "primNatPlus"	    |-> mkPrimFun2 ((+)			    :: Op Nat)
    , "primNatMinus"	    |-> mkPrimFun2 ((\x y -> max 0 (x - y)) :: Op Nat)
    , "primNatTimes"	    |-> mkPrimFun2 ((*)			    :: Op Nat)
    , "primNatDivSucAux"    |-> mkPrimFun4 ((\k m n j -> k + div (max 0 $ n + m - j) (m + 1)) :: Nat -> Nat -> Nat -> Nat -> Nat)
    , "primNatModSucAux"    |->
        let aux :: Nat -> Nat -> Nat -> Nat -> Nat
            aux k m n j | n > j     = mod (n - j - 1) (m + 1)
                        | otherwise = k + n
        in mkPrimFun4 aux
    , "primNatEquality"	    |-> mkPrimFun2 ((==)		    :: Rel Nat)
    , "primNatLess"	    |-> mkPrimFun2 ((<)			    :: Rel Nat)
    , "primLevelZero"	    |-> mkPrimLevelZero
    , "primLevelSuc"	    |-> mkPrimLevelSuc
    , "primLevelMax"	    |-> mkPrimLevelMax

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
    , "primCharEquality"    |-> mkPrimFun2 ((==) :: Rel Char)
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
    , "primCharToNat"       |-> mkPrimFun1 (fromIntegral . fromEnum :: Char -> Nat)
    , "primNatToChar"       |-> mkPrimFun1 (toEnum . fromIntegral   :: Nat -> Char)
    , "primShowChar"	    |-> mkPrimFun1 (Str . show . pretty . LitChar noRange)

    -- String functions
    , "primStringToList"    |-> mkPrimFun1 unStr
    , "primStringFromList"  |-> mkPrimFun1 Str
    , "primStringAppend"    |-> mkPrimFun2 (\s1 s2 -> Str $ unStr s1 ++ unStr s2)
    , "primStringEquality"  |-> mkPrimFun2 ((==) :: Rel Str)
    , "primShowString"	    |-> mkPrimFun1 (Str . show . pretty . LitString noRange . unStr)

    -- Reflection
    , "primQNameType"       |-> primQNameType
    , "primQNameDefinition" |-> primQNameDefinition
    , "primDataConstructors"|-> primDataConstructors

    -- Other stuff
    , "primTrustMe"         |-> primTrustMe
    , "primQNameEquality"  |-> mkPrimFun2 ((==) :: Rel QName)
    ]
    where
	(|->) = (,)

lookupPrimitiveFunction :: String -> TCM PrimitiveImpl
lookupPrimitiveFunction x =
    case Map.lookup x primitiveFunctions of
	Just p	-> liftTCM p
	Nothing	-> typeError $ NoSuchPrimitiveFunction x

lookupPrimitiveFunctionQ :: QName -> TCM (String, PrimitiveImpl)
lookupPrimitiveFunctionQ q = do
  let s = case qnameName q of
            Name _ x _ _ -> show x
  PrimImpl t pf <- lookupPrimitiveFunction s
  return (s, PrimImpl t $ pf { primFunName = q })

