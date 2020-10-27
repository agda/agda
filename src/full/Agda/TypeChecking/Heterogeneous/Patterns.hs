{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}

module Agda.TypeChecking.Heterogeneous.Patterns where

import Agda.TypeChecking.Monad
import qualified Agda.Syntax.Internal as I
import qualified Agda.TypeChecking.Substitute.Class as I

-- * Patterns

pattern El :: Het side (I.Sort' t) -> Het side a -> Het side (I.Type'' t a)
pattern El a b <- Het (I.El (Het -> a)   (Het   -> b))
  where El a b =  Het (I.El (unHet a) (unHet b))
#if __GLASGOW_HASKELL__ >= 802
{-# COMPLETE El #-}
#endif

pattern EmptyTel :: Het side (I.Tele a)
pattern EmptyTel =  Het I.EmptyTel
pattern ExtendTel :: Het side a -> Het side (I.Abs (I.Tele a)) -> Het side (I.Tele a)
pattern ExtendTel a b <- Het (I.ExtendTel (Het -> a) (Het   -> b))
  where ExtendTel a b =  Het (I.ExtendTel (unHet a)  (unHet b))
#if __GLASGOW_HASKELL__ >= 802
{-# COMPLETE EmptyTel, ExtendTel #-}
#endif

absBody :: (I.Subst a) => Het s (I.Abs a) -> Het s a
absBody x = fmap I.absBody x

