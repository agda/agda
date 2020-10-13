-- Andreas, 2020-09-09, issue #4880
-- Parse all interleavings of hiding and irrelevance in non-dependent function space

module Issue4880 (A B : Set) where

postulate
  -- dependent
  -- * visible
  _ : A →   (_ : B) → A
  _ : A →  .(_ : B) → A
  _ : A → ..(_ : B) → A
  -- * hidden
  _ : A →   {_ : B} → A
  _ : A →  .{_ : B} → A
  _ : A → ..{_ : B} → A
  -- * instance
  _ : A →   ⦃ _ : B ⦄ → A
  _ : A →  .⦃ _ : B ⦄ → A
  _ : A → ..⦃ _ : B ⦄ → A

  -- non-dependent
  -- * visible
  _ : A →   B → A
  _ : A →  .B → A
  _ : A → ..B → A
  -- * visible, parenthesized
  _ : A →  .(B) → A
  _ : A → ..(B) → A
  _ : A →  (.B) → A
  _ : A → (..B) → A
  -- * hidden
  _ : A →   {B} → A
  _ : A →  .{B} → A
  _ : A → ..{B} → A
  _ : A →  {.B} → A
  _ : A → {..B} → A
  -- * instance
  _ : A →   ⦃ B ⦄ → A
  _ : A →  .⦃ B ⦄ → A
  _ : A → ..⦃ B ⦄ → A
  _ : A →  ⦃ .B ⦄ → A
  _ : A → ⦃ ..B ⦄ → A
