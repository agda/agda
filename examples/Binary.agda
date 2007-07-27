
{-
   FP Lunch, Nottingham
   July 27, 2007
   Conor McBride
-}

module Binary where

data Bit : Set where
  O : Bit
  I : Bit

infixl 80 _◃_

data Pos : Set where
  ◃I  : Pos
  _◃_ : Pos -> Bit -> Pos

bsuc : Pos -> Pos
bsuc ◃I      = ◃I ◃ O
bsuc (n ◃ O) = n ◃ I
bsuc (n ◃ I) = bsuc n ◃ O

data Peano : Pos -> Set where
  pI   : Peano ◃I
  psuc : {n : Pos} -> Peano n -> Peano (bsuc n)

pdouble : {n : Pos} -> Peano n -> Peano (n ◃ O)
pdouble pI       = psuc pI
pdouble (psuc p) = psuc (psuc (pdouble p))

peano : (n : Pos) -> Peano n
peano ◃I      = pI
peano (n ◃ O) = pdouble (peano n)
peano (n ◃ I) = psuc (pdouble (peano n))

-- Slow addition (yay!)
_+_ : Pos -> Pos -> Pos
_+_ n m = peano n ⊕ m
  where
    _⊕_ : {n : Pos} -> Peano n -> Pos -> Pos
    pI     ⊕ m = bsuc m
    psuc p ⊕ m = bsuc (p ⊕ m)

infixl 60 _+_
infix  40 _==_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

test : (◃I ◃ I ◃ O ◃ O ◃ O) == (◃I ◃ I ◃ O ◃ I) + (◃I ◃ O ◃ I ◃ I)
test = refl
