
module Name where

import Data.Monoid
import Stack

type Name = Stack (String, Int)

infixl 7 <:

(<:) :: Name -> String -> Name
me <: s = me :< (s, 0)

nm :: String -> Name
nm s = Empty <: s

type Agency agent = Name -> agent
