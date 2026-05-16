open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Nat

data ⊥ : Set where
data Unit : Set where
  tt* : Unit

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

{-# BUILTIN INTEGER       Int    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

mutual
  foo : Unit → Int → String
  foo tt* x = primShowInteger x

  primitive
    primShowInteger : Int → String

wuh : ∀ b x y → foo b x ≡ foo b y
wuh b x y = refl

lol : ⊥
lol with () ← wuh tt* (pos 0) (pos 1)
