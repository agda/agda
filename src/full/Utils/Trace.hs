
module Utils.Trace where

import Control.Monad

type Trace = CurrentCall
type SiblingCall = ChildCall

data CurrentCall a
    = Current a (ParentCall a) [SiblingCall a] [ChildCall a]
    | TopLevel [ChildCall a]
data ParentCall a
    = Parent  a (ParentCall a) [SiblingCall a]
    | NoParent
data ChildCall a = Child a [ChildCall a]

newCall :: a -> Trace a -> Trace a
newCall c (TopLevel cs)	       = Current c NoParent cs []
newCall c (Current c' p ss cs) = Current c (Parent c' p ss) cs []

updateCall :: a -> Trace a -> Trace a
updateCall c (TopLevel _)	 = error $ "updateCall: no a in progress"
updateCall c (Current _ p ss cs) = case p of
    NoParent	     -> TopLevel $ Child c cs : ss
    Parent c' p' ss' -> Current c' p' ss' $ Child c cs : ss

matchCall :: (call -> Maybe a) -> Trace call -> Maybe a
matchCall f = matchTrace f'
    where
	f' (Child c _) = f c

matchTrace :: (ChildCall call -> Maybe a) -> Trace call -> Maybe a
matchTrace f (TopLevel _) = Nothing
matchTrace f t@(Current c _ _ cs) =
    f (Child c cs) `mplus` matchTrace f (updateCall c t)

