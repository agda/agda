{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.Heterogeneous where

import Data.Data (Data, Typeable)
import Data.Sequence (Seq)

import Agda.TypeChecking.Free.Lazy (Free)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (TermLike)

import Agda.Utils.Size (Sized)

data TwinT'' a b
instance (Data a, Data b) => Data (TwinT'' a b)
instance (Show a, Show b) => Show (TwinT'' a b)
instance Functor (TwinT'' b)
instance Foldable (TwinT'' b)

type TwinT' = TwinT'' Bool

type TwinT = TwinT' Type

data HetSide = LHS | RHS | Compat | Whole | Both

newtype Het (side :: HetSide) t = Het { unHet :: t }
instance (Typeable side, Data t) => Data (Het side t)
instance Show t => Show (Het side t)
instance TermLike t => TermLike (Het side t)
instance Functor (Het side)

newtype ContextHet = ContextHet { unContextHet :: Seq (Name, Dom TwinT) }
instance Data ContextHet
