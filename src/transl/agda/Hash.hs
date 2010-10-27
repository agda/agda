{-| Provides 'hash' function for many data types
-}
module Hash(Hash, combineHash, emptyHash, hashToInt, hashToMax, Hashable(..)) where
--
-- Hash a value.  Hashing produces an Int of
-- unspecified range.
--
import Data.Array
import Data.Complex
import Data.Ratio



newtype Hash = H Int deriving (Eq)

----instance Show Hash where
--    showsType _ = showString "Hash"

combineHash :: Hash -> Hash -> Hash
combineHash (H x) (H y) = H (x+y)

emptyHash :: Hash
emptyHash = H 0

class Hashable a where
    hash :: a -> Hash

instance Hashable Char where
    hash x = H $ fromEnum x

instance Hashable Int where
    hash x = H $ x

instance Hashable Integer where
    hash x = H $ fromInteger x

instance Hashable Float where
    hash x = H $ truncate x

instance Hashable Double where
    hash x = H $ truncate x

instance Hashable (IO a) where
    hash x = H 0

instance Hashable () where
    hash x = H 0

instance Hashable (a -> b) where
    hash x = H 0

instance (Hashable a) => Hashable (Maybe a) where
    hash Nothing = H 0
    hash (Just x) = hash x

instance (Hashable a, Hashable b) => Hashable (Either a b) where
    hash (Left x) = hash x
    hash (Right y) = hash y


-- Denna bör inte vara bortkommenterad men jag kunde inte
-- göra en instans med String nedan
--instance Hashable a => Hashable [a] where
--    hash l = H $ f l 0
--      where f :: (Hashable a) => [a] -> Int -> Int
--            f [] r = r
--            f (c:cs) r = f cs (3*r + (case hash ( c ) of H h -> h) )


instance (Hashable a,Enum a) => Hashable [a] where
    hash l = H $ f l 0
        where f :: Enum b => [b] -> Int -> Int
              f [] r = r
              f (c:cs) r = f cs (3*r + fromEnum c)


instance (Hashable a, Hashable b) => Hashable (a,b) where
    hash (a,b) = H $ (case hash ( a ) of H h -> h)  + 3 * (case hash ( b ) of H h -> h)

instance (Hashable a, Hashable b, Hashable c) => Hashable (a,b,c) where
    hash (a,b,c) = H $ (case hash ( a ) of H h -> h)  + 3 * (case hash ( b ) of H h -> h)  + 5 * (case hash ( c ) of H h -> h)

instance (Hashable a, Hashable b, Hashable c, Hashable d) => Hashable (a,b,c,d) where
    hash (a,b,c,d) = H $ (case hash ( a ) of H h -> h)  + 3 * (case hash ( b ) of H h -> h)  + 5 * (case hash ( c ) of H h -> h)  + 7 * (case hash ( d ) of H h -> h)

instance (Hashable a, Hashable b, Hashable c, Hashable d, Hashable e) => Hashable (a,b,c,d,e) where
    hash (a,b,c,d,e) = H $ (case hash ( a ) of H h -> h)  + 3 * (case hash ( b ) of H h -> h)  + 5 * (case hash ( c ) of H h -> h)  + 7 * (case hash ( d ) of H h -> h)  + 9 * (case hash ( e ) of H h -> h)

instance Hashable Bool where
    hash False = H 0
    hash True = H 1

instance (Integral a, Hashable a) => Hashable (Ratio a) where
    hash x = H $ (case hash ( denominator x ) of H h -> h)  + (case hash ( numerator x ) of H h -> h)

instance (RealFloat a, Hashable a) => Hashable (Complex a) where
    hash (x :+ y) = H $ (case hash ( x ) of H h -> h)  + (case hash ( y ) of H h -> h)

instance (Ix a) => Hashable (Array a b) where
    hash x = H $ 0 -- !!!

hashToInt :: Int -> Hash -> Int
hashToInt maxhash x =
    case x of
    H h ->
        if h < 0 then
            if -h < 0 then 0
            else (-h) `rem` maxhash
        else h `rem` maxhash

hashToMax maxhash x =
    case hash x of
    H h ->
        if h < 0 then
            if -h < 0 then 0
            else (-h) `rem` maxhash
        else h `rem` maxhash
