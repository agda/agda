{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Reduce where

import Agda.Syntax.Common (Arg)
import Agda.Syntax.Internal (Term, Type, Sort, Elims, QName, Abs)
import Agda.TypeChecking.Monad.Base (TCM, Reduced, MonadReduce)
import Agda.TypeChecking.Substitute.Class (Subst)

reduceDefCopyTCM :: QName -> Elims -> TCM (Reduced () Term)

class Reduce t

instance Reduce Term
instance Reduce Type
instance Reduce Sort
instance Reduce a => Reduce (Arg a)
instance (Subst a, Reduce a) => Reduce (Abs a)

reduce :: (Reduce a, MonadReduce m) => a -> m a
