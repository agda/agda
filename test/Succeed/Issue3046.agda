
data ⊤ : Set where
  tt : ⊤

data Identity (t : Set) : Set where
  MkIdentity : t → Identity t

let-example : Identity ⊤
let-example =
  let x = tt
      in MkIdentity x   -- Parse error

do-example : Identity ⊤
do-example = do
  MkIdentity tt
  where
    x : ⊤
    x = tt
