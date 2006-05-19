{-| Some folding combinators (also monadic ones) for lists.  Nothing
Agda specific. -}

module AgdaScans where

--foldBoth :: (l -> r -> a -> (r, l) -> l -> r -> [a] -> (r, l)
--mapAccumBoth :: (b -> c -> a -> (b, c, d)) -> b -> c -> [a] -> (b, c, [d])

mapAccumL :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumL f s []     = (s, [])
mapAccumL f s (x:xs) = (s'', y:ys)
    where (s',  y)   = f s x
          (s'', ys)  = mapAccumL f s' xs



mapAccumR :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumR f s []     = (s, [])
mapAccumR f s (x:xs) = (s'', y:ys)
    where (s'',  y)  = f s' x
          (s',  ys)  = mapAccumR f s xs




mapMAccumL :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m(a,[c])
mapMAccumL f s [] = return (s,[])
mapMAccumL f s (x:xs) = do (s',  y) <- f s x
                           (s'',ys) <- mapMAccumL f s' xs
                           return (s'', y:ys)


mapMAccumR :: Monad m => (a -> b -> m (a, c)) -> a -> [b] -> m (a, [c])
mapMAccumR f s []     = return (s, [])
mapMAccumR f s (x:xs) = do (s',  ys) <- mapMAccumR f s xs
                           (s'',  y) <- f s' x
                           return (s'', y:ys)
