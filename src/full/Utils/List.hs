
module Utils.List where

maybePrefixMatch :: Eq a => [a] -> [a] -> Maybe [a]
maybePrefixMatch []    rest = Just rest
maybePrefixMatch (_:_) []   = Nothing
maybePrefixMatch (p:pat) (r:rest)
  | p == r    = maybePrefixMatch pat rest
  | otherwise = Nothing

