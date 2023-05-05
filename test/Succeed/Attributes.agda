-- Andreas, 2018-06-14, issue #2513, parsing attributes

{-# OPTIONS --erasure #-}

-- Run-time only use.

postulate
  @0      RT₁ : Set
  @erased RT₂ : Set

-- Default: unrestricted use.

postulate
  @ω      CT₁ : Set
  @plenty CT₂ : Set

-- Irrelevance.

postulate
  .           I₀ : Set
  @irr        I₁ : Set
  @irrelevant I₂ : Set

-- Shape-irrelevance

postulate
  -- .. SI₀ : Set -- Does not parse (yet).
  @shirr            SI₁ : Set
  @shape-irrelevant SI₂ : Set

-- Relevance (default).

postulate
  R₀ : Set
  @relevant R₁ : Set

-- Mix.

postulate
  @0 @shape-irrelevant M : Set

-- In function spaces and telescopes.

@ω id : ∀{@0 A : Set} → @relevant @ω A → A
id x = x

data Wrap (@0 A : Set) : Set where
  wrap' : @relevant A → Wrap A

wrap : ∀ (@0 A) → A → Wrap A
wrap A x = wrap' x

-- In record fields.

record Squash (@0 A : Set) : Set where
  no-eta-equality
  constructor squash
  field
    @irrelevant squashed : A
