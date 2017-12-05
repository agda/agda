module Issue2749-2 where

-- testing unicode lambda and arrow
id : {A : Set} -> A -> A
id = {!!}

-- testing unicode double braces
it : {A : Set} {{a : A}} → A → A
it = {!!}

data B : Set where
  mkB : B → B → B

-- testing unicode suffixes
left : B → B
left b₁ = {!!}
