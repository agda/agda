{-# OPTIONS -v treeless.opt.final:20 -v 0 #-}
module Word where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Word renaming (primWord64ToNat to toNat)
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.IO
open import Agda.Builtin.FromNat
open import Agda.Builtin.String
open import Agda.Builtin.Strict

instance
  NumWord : Number Word64
  Number.Constraint NumWord _ = ⊤
  fromNat {{NumWord}} n = primWord64FromNat n

  NumNat : Number Nat
  Number.Constraint NumNat _ = ⊤
  fromNat {{NumNat}} n = n

natOp : (Nat → Nat → Nat) → Word64 → Word64 → Word64
natOp f a b = fromNat (f (toNat a) (toNat b))
{-# INLINE natOp #-}

_^_ : Nat → Nat → Nat
a ^ zero = 1
a ^ suc n = a * a ^ n

2⁶⁴ : Nat
2⁶⁴ = 2 ^ 64
{-# STATIC 2⁶⁴ #-}

addWord : Word64 → Word64 → Word64
addWord = natOp _+_

subWord : Word64 → Word64 → Word64
subWord = natOp λ a b → a + 2⁶⁴ - b

mulWord : Word64 → Word64 → Word64
mulWord = natOp _*_

{-# INLINE addWord #-}
{-# INLINE subWord #-}
{-# INLINE mulWord #-}

-- div/mod

data ⊥ : Set where

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤

div : (a b : Nat) {{nz : NonZero b}} → Nat
div a 0 {{}}
div a (suc b) = div-helper 0 b a b

mod : (a b : Nat) {{nz : NonZero b}} → Nat
mod a 0 {{}}
mod a (suc b) = mod-helper 0 b a b

{-# INLINE div #-}
{-# INLINE mod #-}

NonZeroWord : Word64 → Set
NonZeroWord a = NonZero (toNat a)

divWord : (a b : Word64) {{nz : NonZeroWord b}} → Word64
divWord a b = fromNat (div (toNat a) (toNat b))

modWord : (a b : Word64) {{nz : NonZeroWord b}} → Word64
modWord a b = fromNat (mod (toNat a) (toNat b))

{-# INLINE divWord #-}
{-# INLINE modWord #-}

-- Comparison --

eqWord : Word64 → Word64 → Bool
eqWord a b = toNat a == toNat b

ltWord : Word64 → Word64 → Bool
ltWord a b = toNat a < toNat b

{-# INLINE eqWord #-}
{-# INLINE ltWord #-}

postulate
  showWord : Word64 → String
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC showWord = Data.Text.pack . show #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

{-# COMPILE JS showWord = function(x) { return x.toString(); } #-}
{-# COMPILE JS putStrLn = function (x) { return function(cb) { process.stdout.write(x + "\n"); cb(0); }; } #-}

2^63 : Word64
2^63 = addWord 1 (divWord (subWord 0 1) 2)

test : Word64
test = addWord (addWord 2^63 100)
               (addWord 2^63 1)

prf : test ≡ 101
prf = refl

prf' : eqWord test 101 ≡ true
prf' = refl

main : IO ⊤
main = putStrLn (showWord test)

-- Some checks for treeless optimisations

ltDouble : Word64 → Word64 → Bool
ltDouble x y = ltWord (mulWord 2 x) y

lt4x : Word64 → Word64 → Bool
lt4x x y = primForce (mulWord 2 x) ltDouble y
