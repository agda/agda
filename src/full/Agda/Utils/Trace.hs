{-# LANGUAGE DeriveDataTypeable #-}
module Agda.Utils.Trace where

import Control.Monad
import Data.Monoid
import Data.Generics (Typeable, Data)

type Trace = CurrentCall
type SiblingCall = ChildCall

data CurrentCall a
    = Current a (ParentCall a) [SiblingCall a] [ChildCall a]
    | TopLevel [ChildCall a]
  deriving (Typeable, Data)
data ParentCall a
    = Parent  a (ParentCall a) [SiblingCall a]
    | NoParent
  deriving (Typeable, Data)
data ChildCall a = Child a [ChildCall a]
  deriving (Typeable, Data)

newCall :: a -> Trace a -> Trace a
newCall c (TopLevel cs)	       = Current c NoParent cs []
newCall c (Current c' p ss cs) = Current c (Parent c' p ss) cs []

updateCall :: a -> Trace a -> Trace a
updateCall c (TopLevel _)	 = error $ "updateCall: no a in progress"
updateCall c (Current _ p ss cs) = case p of
    NoParent	     -> TopLevel $ Child c cs : ss
    Parent c' p' ss' -> Current c' p' ss' $ Child c cs : ss

matchCall :: (call -> Maybe a) -> Trace call -> Maybe a
matchCall f tr = case matchTrace f' tr of
    []	  -> Nothing
    x : _ -> Just x
    where
	f' (Child c _) = maybe [] (:[]) $ f c

matchCalls :: (call -> Maybe a) -> Trace call -> [a]
matchCalls f = matchTrace f'
  where
    f' (Child c _) = maybe [] (:[]) $ f c

matchTrace :: Monoid m => (ChildCall call -> m) -> Trace call -> m
matchTrace f (TopLevel _) = mempty
matchTrace f t@(Current c _ _ cs) =
    f (Child c cs) `mappend` matchTrace f (updateCall c t)

