
{-| Utitlity functions on lists.
-}
module Utils.List where

type Prefix a = [a]
type Suffix a = [a] 

-- | Check if a list has a given prefix. If so, return the list
--   minus the prefix.
maybePrefixMatch :: Eq a => Prefix a -> [a] -> Maybe (Suffix a)
maybePrefixMatch []    rest = Just rest
maybePrefixMatch (_:_) []   = Nothing
maybePrefixMatch (p:pat) (r:rest)
  | p == r    = maybePrefixMatch pat rest
  | otherwise = Nothing

-- | Split a list into sublists. Generalisation of the prelude function
--   @words@.
--
--   > words xs == wordsBy isSpace xs
wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy p xs = yesP xs
    where
	yesP xs = noP (dropWhile p xs)

	noP []	= []
	noP xs	= ys : yesP zs
	    where
		(ys,zs) = break p xs

-- | Chop up a list in chunks of a given length.
chop :: Int -> [a] -> [[a]]
chop _ [] = []
chop n xs = ys : chop n zs
    where (ys,zs) = splitAt n xs

-- | Check whether all elements in a list are distinct from each other.
distinct :: Eq a => [a] -> Bool
distinct []	= True
distinct (x:xs) = x `notElem` xs && distinct xs

-- | Check whether all elements in a list are equal.
allEqual :: Eq a => [a] -> Bool
allEqual []	= True
allEqual (x:xs) = all (x==) xs

