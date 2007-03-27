
module bad where

data One : Set where
  unit : One

T : One -> Set
T unit = One

id : {x : One} -> T x -> T x
id {x} t = t

bad : (x : One) -> T x -> T x
bad unit t = id t

