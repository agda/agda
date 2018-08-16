module Issue1351 where

open import Common.Equality
open import Common.Prelude

f1 : Nat → Nat
f1 x = x + x

f2 : Nat → Nat
f2 x = f1 (f1 x)

f4 : Nat → Nat
f4 x = f2 (f2 x)

f8 : Nat → Nat
f8 x = f4 (f4 x)

f16 : Nat → Nat
f16 x = f8 (f8 x)

f32 : Nat → Nat
f32 x = f16 (f16 x)

thm : f32 1 ≡ 4294967296
thm = refl
