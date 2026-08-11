{-# OPTIONS --cubical --local-rewriting #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
open import Agda.Builtin.Bool renaming (true to tt; false to ff)

-- Arguably, this test demonstrates a bug, but at least Agda warns about
-- 'ConfluenceForCubicalNotSupported'

-- Allowing interval variables in global rewrite rules is dangerous because
-- these variables can get substituted by primitives like 'primHComp'

-- Unlike local rewrite rules though, we don't IMPOSSIBLE

{-# BUILTIN REWRITE _≡_ #-}

variable
  A : Set _
  x : A

postulate
  bad : tt ≡ ff

refl : x ≡ x
refl {x = x} i = x

module Bad (i : I) (@rewrite rw : bad i ≡ tt) where
  prf : bad i ≡ tt
  prf = refl

  foo : Bool
  foo = primHComp {φ = i}
    (λ where j (i = i1) →
              let test : bad i ≡ tt
                  test = {!!} -- Inlining 'prf' here fails!
              in tt)
    tt

_ = {!!}
