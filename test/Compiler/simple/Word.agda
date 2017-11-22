{-# OPTIONS -v treeless:20 #-}
module Word where

open import Agda.Builtin.Nat
open import Agda.Builtin.Word renaming (primWord64ToNat to toNat)
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.IO
open import Agda.Builtin.FromNat
open import Agda.Builtin.String

instance
  NumWord : Number Word64
  Number.Constraint NumWord _ = ⊤
  fromNat {{NumWord}} n = primWord64FromNat n

natOp : (Nat → Nat → Nat) → Word64 → Word64 → Word64
natOp f a b = fromNat (f (toNat a) (toNat b))
{-# INLINE natOp #-}

addWord : Word64 → Word64 → Word64
addWord = natOp _+_

postulate
  showWord : Word64 → String
  putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC showWord = Data.Text.pack . show #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

{-# COMPILE JS showWord = function(x) { return x.toString(); } #-}
{-# COMPILE JS putStrLn = function (x) { return function(cb) { process.stdout.write(x + "\n"); cb(0); }; } #-}

test : Word64
test = addWord 9223372036854775908 9223372036854775809

prf : test ≡ 101
prf = refl

main : IO ⊤
main = putStrLn (showWord test)
