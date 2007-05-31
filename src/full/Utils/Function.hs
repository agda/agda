
module Utils.Function where

on :: (a -> a -> b) -> (c -> a) -> c -> c -> b
on f g x y = f (g x) (g y)

-- | @'iterate'' n f x@ applies @f@ to @x@ @n@ times and returns the
-- result.
--
-- The applications are calculated strictly.

iterate' :: Integral i => i -> (a -> a) -> a -> a
iterate' 0 f x             = x
iterate' n f x | n > 0     = iterate' (n - 1) f $! f x
               | otherwise = error "iterate': Negative input."
