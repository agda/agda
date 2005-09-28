
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
wordsBy p xs = wordsBy' p (dropWhile p xs)
    where
	wordsBy' p []	= []
	wordsBy' p xs	= ys : wordsBy p zs
	    where
		(ys,zs) = break p xs

