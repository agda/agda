module Agda.Termination.Utils where

sepBy :: String -> [String] -> String
sepBy sep [] = ""
sepBy sep (s:ss) = s ++ sep ++ sepBy sep ss

mapMM :: Monad m => (a->m())-> [a] -> m ()
mapMM f [] = return ()
mapMM f (x:xs) = f x >> mapMM f xs

