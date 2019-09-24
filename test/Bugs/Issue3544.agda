
-- Fails (gracefully) after #3903 damage control.
-- Should succeed once #3903 is fixed properly.

data Nat : Set where
  succ : Nat → Nat

data Fin : Nat → Set where
  zero : (n : Nat) → Fin (succ n)

data Tm (n : Nat) : Set where
  var : Fin n → Tm n
  piv : Fin (succ n) → Tm n

data Cx : Nat → Set where
  succ : (n : Nat) → Tm n → Cx (succ n)

data CxChk : ∀ n → Cx n → Set where
  succ : (n : Nat) (T : Tm n) → CxChk (succ n) (succ n T)

data TmChk (n : Nat) : Cx n → Tm n → Set where
  vtyp : (g : Cx n) (v : Fin n) → CxChk n g → TmChk n g (var v)

error : ∀ n g s → TmChk n g s → Set
error n g s (vtyp g' (zero x) (succ n' (piv (zero y)))) =  Nat -- Internal error here.
error _ _ _ (vtyp g' (zero n) (succ n (var x))) = Nat -- This clause added to pass 2.5.3.
