{-# LANGUAGE TypeSynonymInstances #-}
module Agda.Utils.Serialise where

import Control.Monad
import Data.Generics
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Either
import qualified Data.ByteString.Lazy as BS
import Data.ByteString.Lazy (ByteString)

import Agda.Utils.Tuple
import Agda.Utils.Unicode

newtype Printer a = Printer { runPrinter :: a -> ShowS }
newtype Parser  a = Parser  { runParser :: ByteString -> (a, ByteString) }

data IFun a b = IFun (a -> b) (b -> a)

class BiMonad m where
    charS   :: m Char
    stringS :: Int -> m String
    returnS :: a -> m a
    bindS   :: (b -> a) -> m a -> (a -> m b) -> m b

instance BiMonad Printer where
    charS = Printer (:)
    stringS _ = Printer $ \s rest -> toUTF8 s ++ rest
    returnS _ = Printer $ const id
    bindS mkA (Printer prA) k =
	Printer $ \b -> let a = mkA b in prA a . runPrinter (k a) b

bsToString :: ByteString -> String
bsToString = fromUTF8 . map (toEnum . fromIntegral) . BS.unpack

instance BiMonad Parser where
    charS		 = Parser $ \s -> (toEnum . fromIntegral $ BS.head s, BS.tail s)
    stringS n		 = Parser $ \s -> let (s0,rest) = BS.splitAt (fromIntegral n) s
					  in (bsToString s0, rest)
    returnS x		 = Parser $ \s -> (x,s)
    bindS _ (Parser m) k = Parser $ \s -> let (x,s') = m s in runParser (k x) s'

mapS :: BiMonad m => IFun a b -> m a -> m b
mapS (IFun f g) sa = bindS g sa $ returnS . f

(>->) :: BiMonad m => m a -> m b -> m (a,b)
sa >-> sb = bindS fst sa $ \a -> 
	    bindS snd sb $ \b ->
	    returnS (a,b)

sequenceS :: BiMonad m => [m a] -> m [a]
sequenceS []	 = returnS []
sequenceS (s:ss) =
    bindS head s	      $ \x ->
    bindS tail (sequenceS ss) $ \xs ->
    returnS (x : xs)

replicateS :: BiMonad m => Int -> m a -> m [a]
replicateS n = sequenceS . replicate n

class Serialisable a where
    serialiser :: BiMonad m => m a

instance Serialisable () where
    serialiser = returnS ()

instance Serialisable Char where
    serialiser = {-# SCC "charS" #-} charS

instance Serialisable Int where
    serialiser = {-# SCC "intS" #-} bindS small serialiser $ \c -> case c of
	'\255'	-> mapS (fromChars `IFun` toChars) $ replicateS nChars serialiser
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
    serialiser = mapS (IFun (\(x,(y,z)) -> (x,y,z)) (\(x,y,z) -> (x,(y,z))))
		 serialiser

instance (Serialisable a, Serialisable b, Serialisable c, Serialisable d)
	=> Serialisable (a,b,c,d) where
    serialiser = mapS (IFun (\((x,y),(z,w)) -> (x,y,z,w)) (\(x,y,z,w) -> ((x,y),(z,w))))
		 serialiser

instance (Serialisable a, Serialisable b, Serialisable c, Serialisable d, Serialisable e)
	=> Serialisable (a,b,c,d,e) where
    serialiser = mapS (IFun (\((x,y),(z,w,u)) -> (x,y,z,w,u)) (\(x,y,z,w,u) -> ((x,y),(z,w,u))))
		 serialiser

instance (Serialisable a, Serialisable b, Serialisable c, Serialisable d, Serialisable e, Serialisable f)
	=> Serialisable (a,b,c,d,e,f) where
    serialiser = mapS (IFun (\((x,y,v),(z,w,u)) -> (x,y,v,z,w,u)) (\(x,y,v,z,w,u) -> ((x,y,v),(z,w,u))))
		 serialiser

instance Serialisable String where
    serialiser = {-# SCC "stringS" #-} bindS (length . toUTF8) serialiser stringS

instance Serialisable a => Serialisable [a] where
    serialiser = {-# SCC "listS" #-} bindS length serialiser $ \n -> replicateS n serialiser

instance (Ord k, Serialisable k, Serialisable v) => Serialisable (Map k v) where
    serialiser = mapS (Map.fromList `IFun` Map.toList) serialiser

serialise :: Serialisable a => a -> String
serialise x = runPrinter serialiser x ""

deserialise :: Serialisable a => ByteString -> a
deserialise s = case deserialiseLazy s of
    (x,True) -> x
    _	     -> error "deserialise: no parse"

-- | Force the Bool to force the a. True means ok and false means left-over garbage.
deserialiseLazy :: Serialisable a => ByteString -> (a, Bool)
deserialiseLazy s = case runParser serialiser s of
    (x, s)  -> (x, BS.null s)

