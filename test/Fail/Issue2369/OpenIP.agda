-- {-# OPTIONS --allow-unsolved-metas #-}

module Issue2369.OpenIP where

test : Set
test = {!!}  -- unsolved interaction point


-- postulate A : {!!}
