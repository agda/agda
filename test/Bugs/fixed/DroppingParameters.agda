
module bug where

data True : Set where
  tt : True

data Sigma (x : True) : Set where
 pair : True -> Sigma x

postulate
  p : True

T : True -> Sigma p -> Set
T tt (pair _) = True

postulate
  S : True -> Sigma p -> Set

z : Sigma p
z = pair p

postulate
  build : (q : Sigma p) -> T p q -> True
  pz    : T p z

