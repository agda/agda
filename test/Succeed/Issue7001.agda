-- Andreas, 2025-08-08, issue #7001, reported by nad w/ testcase.
--
-- In the presence of erasure and other modalities,
-- we should not infer lambdas unless the user provided
-- the modalities at the binder,
-- otherwise we might commit to the wrong modality.

{-# OPTIONS --erasure #-}

-- {-# OPTIONS -v tc.meta:10 #-}
-- {-# OPTIONS -v tc:15 #-}
-- {-# OPTIONS -v tc.term.lambda:30 #-}

record _⇔_ (A B : Set₁) : Set₁ where
  constructor mk
  field
    to   : A → B
    from : B → A

_↝_ : Set₁ → Set₁ → Set₁
A ↝ B = A → B

postulate
  F : (A : Set₁) → A ⇔ (@0 Set → Set) → A ↝ (@0 Set → Set)

module Constructor where

  G : (@0 Set → Set) → (@0 Set → Set)
  G =
    F _
      (mk (λ H A → H A)
          (λ H A → H A))

module OverloadedConstructor where

  record Foo : Set where
    constructor mk

  G : (@0 Set → Set) → (@0 Set → Set)
  G =
    F _
      (mk (λ H A → H A)
          (λ H A → H A))

module RecordExpression where

  G : (@0 Set → Set) → (@0 Set → Set)
  G =
    F _
      (record
         { to   = λ H A → H A
         ; from = λ H A → H A
         })

-- Previously, these failed because some modalities that should have been inferred to @0
-- were inferred to the standard modality @ω.

-- Now, these cases should succeed.
