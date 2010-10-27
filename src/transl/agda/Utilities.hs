{-| Mostly monadic utility functions. Nothing Agda specific. -}

module Utilities where
import PPrint
import Error --(prEMsg)
import Control.Monad
import Monads
import Data.Maybe

infixr 9 `oM`
infixl 2 `phandle`
infixl 2 `phandle_`
infixl 2 `fhandle`
infixl 2 `fhandle_`

mapPair :: (a->b) -> (c->d) -> (a,c) -> (b,d)
mapPair f g (x,y) = (f x,g y)


mapPair' :: (c->d) -> (c,c) -> (d,d)
mapPair' g (x,y) = (g x,g y)


mapPairM :: Monad m => (a -> m b) -> (c -> m d) -> (a,c) -> m (b,d)
mapPairM f g (a,c) = do b <- f a
                        d <- g c
                        return (b,d)

fstM :: Monad m => m (a,b) -> m a
fstM x = do {(a,b) <- x; return a}


foldlM :: (Monad m) => (a -> b -> m b) -> b -> [a] -> m b
foldlM f a [] = return a
foldlM f a (x:xs) = do a' <- f x a
                       foldlM f a' xs

foldrM :: (Monad m) => (a -> b -> m b) -> b -> [a] -> m b
foldrM f a []      = return a
foldrM f a (x:xs)  = do x' <- foldrM f a xs
                        f x x'

untilM_ :: Monad m => m Bool -> (a -> m a) -> a ->  m a
untilM_ p f a = do b <- p
                   if b then return a
                        else do a' <- f a
                                untilM_ p f a'

thenM :: Maybe a -> (a -> Maybe b) -> Maybe b
thenM (Just a ) f = f a
thenM Nothing f = Nothing




build :: (a -> a -> a) -> a -> [a] -> a
build _ u [] = u
build f _ xs = foldr1 f xs

build2 :: (a -> a -> a) -> a -> (b,[a]) -> (b,a)
build2 f u (c,xs) = (c,build f u xs)


mapAccumLM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
mapAccumLM f s [] = return (s,[])
mapAccumLM f s (x:xs) = do
        (s',y) <- f s x
        (s'',ys) <- mapAccumLM f s' xs
        return (s'',y:ys)

mapAccumRM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
mapAccumRM f s [] = return (s,[])
mapAccumRM f s (x:xs) = do
        (s',ys) <- mapAccumLM f s xs
        (s'',y) <- f s' x
        return (s'',y:ys)


-- Utilities

pp :: (PPrint a) => PDetail -> a -> IText
pp d x = pPrint d 0 x

t :: String -> IText
t s = text s

pre m = t ("ERROR:\n"++prEMsg m)



liftMaybeList :: [Maybe a] -> Maybe [a]
liftMaybeList [] = Just []
liftMaybeList ((Just a) : mas) = case liftMaybeList mas of
                                  Nothing -> Nothing
                                  Just as -> Just $ (a:as)
liftMaybeList (Nothing : _) = Nothing


liftMaybePair :: (Maybe a,Maybe b) -> Maybe (a,b)
liftMaybePair (Nothing,_) = Nothing
liftMaybePair (_,Nothing) = Nothing
liftMaybePair (Just a,Just b) = Just (a,b)

-- these must be somewhere already


oM:: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
f `oM` g = \ a -> f =<< (g a)

tM:: Monad m => (a, m b)-> m (a, b)
tM (a,x) = (return . (,) a) =<< x

--

tup_ass ((x,y),z) = (x,(y,z))

-- (for use with =<<)
phandle:: ErrorMonad m => (b -> m a) -> (b -> EMsg -> m a) -> b -> m a
phandle f h b = f b `handle` h b

phandle_ :: ErrorMonad m => (b -> m a) -> (b -> m a) -> b -> m a
phandle_ f h = f `phandle` (\ b err -> h b)

fhandle:: ErrorMonad m => (b -> m a) -> (EMsg -> m a) -> b -> m a
fhandle f h b = f b `handle` h

fhandle_ :: ErrorMonad m => (b -> m a) -> m a -> b -> m a
fhandle_ f h = f `fhandle` (\ _ -> h)

filterM :: ErrorMonad m => (b -> m c) -> [b] -> m [c]
filterM f [] = return []
filterM f l = do l' <- mapM (\x -> mkMaybeError (f x)) l
                 return $ catMaybes l'

--

type Auto a = a -> a
type AutoM a b = b -> a b

-- possibly a useful abbrev to process a tel.

foldMx :: Monad m => (c -> a -> b -> m a) -> a -> [b] -> c -> m a
foldMx f a bs c = foldM (f c) a bs

whenM             :: (Monad m) => m Bool -> m () -> m ()
whenM mp s         =  mp >>= \p -> when p s

unlessM           :: (Monad m) => m Bool -> m () -> m ()
unlessM mp s       =  mp >>= \p -> unless p s
