{-| Mostly list utility functions.  Nothing Agda specific.
-}

module Util where
import Data.List(sort, sortBy, group, groupBy, union, partition)
--import NameSupply

import AgdaTrace
--import IOUtil(progArgs)
--doTrace = elem "-debug" progArgs
--doTrace2 = length (filter (== "-debug") progArgs) > 1

--tracex s x = if doTrace then traces s x else x
--tracex2 s x = if doTrace2 then traces s x else x

traces s x = if s==s then trace s x else undefined


splitBy :: [a->Bool] -> [a] -> [[a]]
splitBy [] _ = []
splitBy (p:ps) xs = let (xs', xs'') = span p xs in xs' : splitBy ps xs''

remDup :: (Eq a) => [a] -> [a]
remDup (x:xxs@(x':_)) = if x==x' then remDup xxs else x:remDup xxs
remDup xs = xs


remDupWith :: (a -> a -> Bool) -> [a] -> [a]
remDupWith f (x:xxs@(x':_)) = if (f x x') then remDupWith f xxs else x:remDupWith f xxs
remDupWith _ xs = xs

unzipWith :: (a -> (b,c)) -> [a] -> ([b], [c])
unzipWith f l = unzip (map f l)

unzipWithM :: Monad m => (a -> m (b,c)) -> [a] -> m ([b], [c])
unzipWithM f l = do xs <- mapM f l
                    return $ unzip xs

unzipWith2 :: (a -> b -> (c, d)) -> [a] -> [b] -> ([c], [d])
unzipWith2 f l1 l2 = unzip (zipWith f l1 l2)

findSame :: (Ord a) => [a] -> [[a]]
findSame = filter ((>1) . length) . group . sort
{-
findSameLe :: (a->a->Bool) -> [a] -> [[a]]
findSameLe le = filter ((>1) . length) . groupBy eq . sortLe le
        where eq x y = le x y && le y x         -- inefficient
-}
-- this is awfully slow!
findSameEq :: (a->a->Bool) -> [a] -> [[a]]
findSameEq eq [] = []
findSameEq eq (x:xs) =
        case partition (eq x) xs of
            ([], ns) -> findSameEq eq ns
            (es, ns) -> (x:es) : findSameEq eq ns

--mapFst f xys = [(f x, y) | (x,y)<-xys]

--mapSnd f xys = [(x, f y) | (x,y)<-xys]

unwordsWith d [] = ""
unwordsWith d [x] = x
unwordsWith d (x:xs) = x++d++unwordsWith d xs

checkEither :: [Either a b] -> Either [a] [b]
checkEither xs = f xs [] []
        where f [] [] rs = Right (reverse rs)
              f [] ls _  = Left  (reverse ls)
              f (Left l :xs) ls rs = f xs (l:ls) rs
              f (Right r:xs) ls rs = f xs ls (r:rs)

joinByFst :: (Ord a) => [(a, b)] -> [(a, [b])]
joinByFst = map (\ xys@((x,_):_) -> (x, map snd xys)) . groupBy (\ (x,_) (y,_) -> x==y) . sortBy (\ (x,_) (y,_) -> x `compare` y)
{-
joinByFstLe :: (a->a->Bool) -> [(a, b)] -> [(a, [b])]
joinByFstLe le = map (\ xys@((x,_):_) -> (x, map snd xys)) . groupBy (\ (x,_) (y,_) -> not (le x y)) . sortLe (\ (x,_) (y,_) -> le x y)
-}
swap (x,y) = (y,x)

my_assert True  msg v = v
my_assert False msg v = error ("assertion failed: "++msg)


type AList a b = [(a, b)]

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (j@(Just _):_) = j
firstJust (_:ms) = firstJust ms

breakAt x xs =
        case span (/= x) xs of
            (ys,_:zs) -> (ys,zs)
            p -> p

mapThd f xyzs = [(x, y, f z) | (x, y, z) <- xyzs]

concatUnzipMap f zs =
        let (xss, yss) = unzip (map f zs)
        in  (concat xss, concat yss)

unions l = foldr union [] l

unJust (Just x) = x


rTake n = reverse . take n . reverse
rDrop n = reverse . drop n . reverse

mDefault s Nothing = s
mDefault s (Just x) = x

apFst f (x, y) = (f x, y)

apSnd f (x, y) = (x, f y)

fst3 (x,_,_) = x
snd3 (_,x,_) = x
thd  (_,_,x) = x

boolCompress [] _  = []
boolCompress _  [] = []
boolCompress (True:bs) (x:xs) = x : boolCompress bs xs
boolCompress (False:bs) (x:xs) = boolCompress bs xs

anySame :: (Ord a) => [a] -> Bool
anySame = same . sort
        where same (x:xs@(x':_)) = x == x' || same xs
              same _ = False

allSame :: (Eq a) => [a] -> Bool
allSame [] = True
allSame (x:xs) = all (==x) xs

mkSet :: (Ord a) => [a] -> [a]
mkSet l = remDup (sort l)


findDup :: (Eq a) => [a] -> [a]
findDup [] = []
findDup (x:xs) =
    case filter (== x) xs of
    [] -> findDup xs
    xs' -> x:xs'

findDupWith :: (a -> a -> Bool) ->  [a] -> [a]
findDupWith _ [] = []
findDupWith f (x:xs) =
    case filter (f x) xs of
    [] -> findDupWith f xs
    xs' -> x:xs'

assoc :: (Eq a) => [(a,b)] -> a -> b
assoc xys x =
    case lookup x xys of
    Just y -> y
    Nothing -> error "assoc"

{-
sortFst xs = sortLe (\(x,_) (y,_) -> x <= y) xs


sortGroup :: (a->a->Bool) -> [a] -> [[a]]
sortGroup le = groupBy (\x y-> le x y && le y x) . sortLe le
-}
