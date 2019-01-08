{-# OPTIONS -v impossible:100 #-}
module Issue882a where

open import Common.Level
open import Common.Equality
open import Agda.Builtin.TrustMe

trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
trustMe = primTrustMe

postulate
  S : Set
  B : Set
  b : B

M : Set
M = B -> S

out : M -> M
out m = o
  where

   s : S
   s = m b

   postulate
     mko : (mm : S) -> s ≡ mm -> M

   o : M
   o n = mko (m b) trustMe n

postulate
  unfold : (M -> M) -> M

inn : M
inn = unfold out

postulate
  n : B

iso1 : inn ≡ inn
iso1 rewrite refl {x = n} = refl
-- iso1 rewrite (refl {a = lzero}{A = B}{x = n}) = refl

{- Error

OLD:
An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Conversion.hs:636

NEW:
Some vomit about Setω not equal to Level when checking well-formedness
of with type.

NEWER (2013-11-30):
Cannot instantiate the metavariable _48 to solution m b since it
contains the variable m which is not in scope of the metavariable
or irrelevant in the metavariable but relevant in the solution
when checking that the type
B →
(w : _x_48 ≡ _x_48) →
unfold (λ m → _.mko m (m b) w) ≡ unfold (λ m → _.mko m (m b) w)
of the generated with function is well-formed

NEVER (2014-05-17):
Rewriting with refl is a no-op, so no error is triggered any more.
Just an unresolved meta now.

NOW (2015-12-25): filled rhs, so now should succeed.
-}
