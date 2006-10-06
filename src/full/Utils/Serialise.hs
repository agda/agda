{-# OPTIONS -fglasgow-exts #-}

module Utils.Serialise where

import Control.Monad
import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Either

import Utils.Tuple

data Serialiser a = Ser (a -> ShowS) (State String a)

data IFun a b = IFun (a -> b) (b -> a)

consI :: IFun (a,[a]) [a]
consI = uncurry (:) `IFun` \ (x:xs) -> (x,xs)

fstI :: b -> IFun (a,b) a
fstI x = fst `IFun` flip (,) x

sndI :: a -> IFun (a,b) b
sndI x = snd `IFun` (,) x

pairL = invI . sndI
pairR = invI . fstI

invI :: IFun a b -> IFun b a
invI (IFun f g) = IFun g f

returnS :: a -> Serialiser a
returnS x = Ser (const id) (return x)

bindS :: (a -> k) -> Serialiser k -> (k -> Serialiser a) -> Serialiser a
bindS key (Ser sk dk) f = Ser ser des
    where
	ser x = sk k . sa x
	    where
		k	 = key x
		Ser sa _ = f k
	des = do
	    k <- dk
	    let Ser _ da = f k
	    da

mapS :: IFun a b -> Serialiser a -> Serialiser b
mapS (IFun f g) sa = bindS g sa $ returnS . f

(>->) :: Serialiser a -> Serialiser b -> Serialiser (a,b)
sa >-> sb = bindS fst sa $ \a -> 
	    bindS snd sb $ \b ->
	    returnS (a,b)

sequenceS :: [Serialiser a] -> Serialiser [a]
sequenceS []	 = returnS []
sequenceS (s:ss) = mapS consI (s >-> sequenceS ss)

replicateS :: Int -> Serialiser a -> Serialiser [a]
replicateS n = sequenceS . replicate n

class Serialisable a where
    serialiser :: Serialiser a

instance Serialisable () where
    serialiser = returnS ()

instance Serialisable Char where
    serialiser = Ser (:) (do x:xs <- get; put xs; return x)

instance Serialisable Int where
    serialiser = bindS small serialiser $ \c -> case c of
	'\255'	-> mapS (fromChars `IFun` toChars) $ sequenceS $ replicate nChars serialiser
	_	-> returnS $ fromEnum c
	where
	    nChars = 4

	    small n | n >= 0 && n < 255	= toEnum n
		    | otherwise		= '\255'

	    toChars :: Int -> [Char]
	    toChars n = map (toEnum . (`mod` 256))
			$ scanl (\n _ -> div n 256) n
			$ replicate (nChars - 1) ()

	    fromChars :: [Char] -> Int
	    fromChars bs = foldr (\b n -> fromEnum b + 256 * n) 0 bs

instance Serialisable Bool where
    serialiser = mapS (fromChar `IFun` toChar) serialiser
	where
	    fromChar 't' = True
	    fromChar 'f' = False
	    fromChar _   = error "deserialise Bool: no parse"
	    toChar True  = 't'
	    toChar False = 'f'

instance Serialisable a => Serialisable (Maybe a) where
    serialiser = bindS code serialiser $ \c -> case c of
		    'j' -> mapS (IFun Just fromJust) serialiser
		    'n' -> returnS Nothing
		    _	-> error "deserialise Maybe: no parse"
	where
	    code Nothing  = 'n'
	    code (Just _) = 'j'

instance (Serialisable a, Serialisable b) => Serialisable (Either a b) where
    serialiser = bindS code serialiser $ \c -> case c of
		    'l' -> mapS (IFun Left  fromLeft ) serialiser
		    'r' -> mapS (IFun Right fromRight) serialiser
		    _	-> error "deserialise Either: no parse"
	where
	    code (Left  _) = 'l'
	    code (Right _) = 'r'
	    fromLeft  (Left x) = x
	    fromLeft  _	       = error "fromLeft"
	    fromRight (Right x) = x
	    fromRight _	       = error "fromRight"

instance (Serialisable a, Serialisable b) => Serialisable (a,b) where
    serialiser = serialiser >-> serialiser

instance (Serialisable a, Serialisable b, Serialisable c) => Serialisable (a,b,c) where
    serialiser = mapS (IFun (\(x,(y,z)) -> (x,y,z)) (\(x,y,z) -> (x,(y,z)))) $
		 serialiser >-> serialiser

instance (Serialisable a, Serialisable b, Serialisable c, Serialisable d)
	=> Serialisable (a,b,c,d) where
    serialiser = mapS (IFun (\((x,y),(z,w)) -> (x,y,z,w)) (\(x,y,z,w) -> ((x,y),(z,w)))) $
		 serialiser >-> serialiser

instance Serialisable a => Serialisable [a] where
    serialiser = bindS length serialiser $ \n -> replicateS n serialiser

instance (Ord k, Serialisable k, Serialisable v) => Serialisable (Map k v) where
    serialiser = mapS (Map.fromList `IFun` Map.toList) serialiser

serialise :: Serialisable a => a -> String
serialise = serialise' serialiser

deserialise :: Serialisable a => String -> a
deserialise = deserialise' serialiser

serialise' :: Serialiser a -> a -> String
serialise' (Ser s _) x = s x ""

deserialise' :: Serialiser a -> String -> a
deserialise' (Ser _ d) s = case runState d s of
    (x,"") -> x
    _	   -> error "deserialise: no parse"

