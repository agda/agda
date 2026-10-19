open import Agda.Builtin.FromString

data Obj : Set where obj : Obj

ex : Obj
ex = {! -u !}
