-- Andreas, 2014-02-11 issue raised by Niccolo Veltri
-- {-# OPTIONS -v term.matrices:40 #-}

open import Common.Equality

data _=⟨_⟩⇒*_ {X : Set}(x : X)(f : X → X) : X → Set where
  done : x =⟨ f ⟩⇒* x
  next : ∀{y z} → f y ≡ z → x =⟨ f ⟩⇒* y → x =⟨ f ⟩⇒* z

trans* : ∀{X}{x y z}{f : X → X} → x =⟨ f ⟩⇒* y → y =⟨ f ⟩⇒* z → x =⟨ f ⟩⇒* z
trans* p done = p
trans* p (next r q) = next r (trans* p q)

const* : ∀{X}{x y}{f : X → X} → x =⟨ f ⟩⇒* y → f x ≡ x → x ≡ y
const* done q = refl
const* (next r p) q with const* p q
const* (next r p) q | refl = trans (sym q) r

bad : ∀{X}{x y z}{f : X → X} → x =⟨ f ⟩⇒* z → f z ≡ x → x =⟨ f ⟩⇒* y →
      y =⟨ f ⟩⇒* x
bad done p q rewrite const* q p = done
bad (next p q) r s =
  next r (bad (trans* (next r done) q) p (trans* (next r done) s))

{- PROBLEM WAS:

Interesting part of original call matrix (argss 2-7 of 0-8)

A
? ? = ? ? ?
? = ? ? ? ?
? ? ? ? < ?
? ? ? = ? ?
? ? ? ? ? ?
? ? ? ? < ?

A2 = A*A
? ? ? ? < ?
? = ? ? ? ?
? ? ? ? ? ?
? ? ? = ? ?
? ? ? ? ? ?
? ? ? ? ? ?

Funny, A4 would be worse than A2 why is ist not continuing to iterate?

==> BUG IN 'notWorse' for call graphs.

======================================================================
======================= Initial call matrices ========================
======================================================================

  Source: 0
  Target: 0
  Matrix: = ? ? ? ? ? ? ? ?
          ? = ? ? ? ? ? ? ?
          ? ? ? ? = ? ? ? ?
          ? ? ? = ? ? ? ? ?
          ? ? ? ? ? ? < ? ?
          ? ? ? ? ? = ? ? ?
          ? ? ? ? ? ? ? ? ?
          ? ? ? ? ? ? < ? ?
          ? ? ? ? ? ? ? ? ?
======================================================================
========================= New call matrices ==========================
======================================================================

  Source: 0
  Target: 0
  Matrix: = ? ? ? ? ? ? ? ?
          ? = ? ? ? ? ? ? ?
          ? ? ? ? ? ? < ? ?
          ? ? ? = ? ? ? ? ?
          ? ? ? ? ? ? ? ? ?
          ? ? ? ? ? = ? ? ?
          ? ? ? ? ? ? ? ? ?
          ? ? ? ? ? ? ? ? ?
          ? ? ? ? ? ? ? ? ?
Idempotent call matrices (no dot patterns):
Other call matrices (no dot patterns):
[the two matrices above]
-}

data Top : Set where
  tt : Top

id : Top → Top
id x = x

loop : tt =⟨ id ⟩⇒* tt
loop = bad (next refl done) refl done

