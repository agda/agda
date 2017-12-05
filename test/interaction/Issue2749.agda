{-# OPTIONS --no-unicode #-}

module Issue2749 where

-- testing ascii only lambda and arrow
id : {A : Set} -> A -> A
id = {!!}

-- testing ascii only double braces
it : {A : Set} {{a : A}} → A → A
it = {!!}

data B : Set where
  mkB : B → B → B

-- testing ascii only suffixes
left : B → B
left b1 = {!!}
