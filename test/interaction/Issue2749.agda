{-# OPTIONS --no-unicode #-}

module Issue2749 where

id : {A : Set} -> A -> A
id = {!!}
