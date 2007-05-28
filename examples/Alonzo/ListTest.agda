module ListTest where
import AlonzoPrelude
import PreludeList
open AlonzoPrelude
open PreludeList
mynil : {A:Set} -> List A
mynil = []

mycons : {A:Set} -> A -> List A -> List A
mycons x xs = x :: xs

head : (A:Set) -> List A -> A
head A (x :: xs) = x

