module Issue358 where

postulate Sigma : Set -> (Set -> Set) -> Set
syntax Sigma A (\x -> B)  = x colon A operator B

postulate T : Set
test = x colon T operator {!!}


