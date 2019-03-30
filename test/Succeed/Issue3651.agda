
data Unit : Set where
  unit : Unit

data Builtin : Set where
  addInteger : Builtin

data SizedTermCon : Set where
  integer : (s : Unit) → SizedTermCon

data ScopedTm : Set where
  con : SizedTermCon → ScopedTm

data Value : ScopedTm → Set where
  V-con : (tcn : SizedTermCon) → Value (con tcn)

BUILTIN : Builtin → (t : ScopedTm) → Value t → Unit
BUILTIN addInteger _ (V-con (integer s)) = s
