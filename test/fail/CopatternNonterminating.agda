{-# OPTIONS --copatterns #-}
-- {-# OPTIONS -v term:20 #-}
-- {-# OPTIONS --no-positivity-check #-}
-- {-# OPTIONS -v tc.def.fun:50  #-}
module CopatternNonterminating where

open import Common.Equality

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
module S = Stream

illdefined : {A : Set} -> Stream A
S.head illdefined = S.head illdefined
S.tail illdefined = S.tail illdefined
-- should not termination-check

{-
illRepeat : {A : Set}(a : A) → Stream A
(       (S.head (illRepeat a))) = a
(S.head (S.tail (illRepeat a))) = a
(S.tail (S.tail (illRepeat a))) = S.tail (S.tail (illRepeat a))
-}

{-
-- deep copattern matches are not yet translated into something
-- that termination checks
illRepeat : {A : Set}(a : A) → Stream A
(       (S.head (illRepeat a))) = a
(S.head (S.tail (illRepeat a))) = a
(S.tail (S.tail (illRepeat a))) = (S.tail (illRepeat a))

record _≈_ {A : Set}(s t : Stream A) : Set where
  field
    head : S.head s ≡ S.head t
    tail : S.tail s ≈ S.tail t
module B = _≈_

repeat : {A : Set}(a : A) → Stream A
S.head (repeat a) = a
S.tail (repeat a) = repeat a

-- THIS SHOULD NOT TERMINATION CHECK WITH CURRENT TRANSLATION SEMANTICS
-- OF COPATTERNS
repeat′ : {A : Set}(a : A) → Stream A
(       (S.head (repeat′ a))) = a
(S.head (S.tail (repeat′ a))) = a
(S.tail (S.tail (repeat′ a))) = S.tail (repeat′ a) -- invalid projection

repeat≈repeat′ : {A : Set}(a : A) → repeat a ≈ repeat′ a
(       (B.head (repeat≈repeat′ a))) = refl
(B.head (B.tail (repeat≈repeat′ a))) = refl
(B.tail (B.tail (repeat≈repeat′ a))) = repeat≈repeat′ a
-}
