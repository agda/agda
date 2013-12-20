
module _ (P : Set) where

data ⊤ : Set where tt : ⊤

foo : ⊤ → Set
foo tt = ⊤

bar : {{_ : ⊤}} → ⊤
bar {{tt}} = tt

error : foo bar → ⊤
error tt = tt
