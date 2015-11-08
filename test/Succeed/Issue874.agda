-- Andreas, 2013-06-22, bug reported by evancavallo
{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS -v tc.conv:20 -v impossible:100 #-}
module Issue874 where

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

module _ {A : Set} where

  postulate
    P : A → Set

  foo : A → Set
  foo _ = Σ (A → A) (λ _ → (∀ _ → A))
    -- the unsolved meta here is essential to trigger the bug

  bar : (x : A) → foo x → Set
  bar x (g , _) = P (g x)

  postulate
    pos : {x : A} → Σ (foo x) (bar x)

  test : {x : A} → Σ (foo x) (bar x)
  test = pos

-- this raised an internal error in Conversion.compareElims
-- when projecting at unsolved record type
