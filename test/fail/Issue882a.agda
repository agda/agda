{-# OPTIONS -v impossible:100 #-}
module Issue882a where

open import Common.Level
open import Common.Equality

private
 primitive
   primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

-- trustMe {x = x} {y = y} evaluates to refl if x and y are
-- definitionally equal.
--
-- For an example of the use of trustMe, see Data.String._≟_.

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
iso1 rewrite refl {x = n} = {!!}
-- iso1 rewrite (refl {a = lzero}{A = B}{x = n}) = {!!}

{- Error

OLD:
An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Conversion.hs:636

NEW:
Some vomit about Setω not equal to Level when checking well-formedness
of with type.
-}



