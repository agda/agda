-- Andreas, 2015-06-11, issue #1560 reported by Peter Thiemann
-- Ulf, 2015-09-23:
--   This test was still taking 12s, which is annoyingly much.
--   I commented out a few of the constructors to bring it down
--   to 2s. With agda-2.4.2 it checks in 18s, which should be long
--   enough to notice.

open import Common.Coinduction

-- Andreas, 2017-04-26: removing fake mutual speeds up from 1.8s to 1.3s
-- However, the purpose of this test is to be slow on old versions of Agda
-- which shows if the fake mutual is present.
-- module _ where
mutual

  -- an stype

  data SType' : Set where
    Skip : SType'
    Semi : ∞ SType' → ∞ SType' → SType'
    Case : ∞ SType' → ∞ SType' → SType'
    c    : (SType' → SType') → SType'

  -- equivalence

  data _∼_ : SType' → SType' → Set where
    ∼-Skip : Skip ∼ Skip
    ∼-Case : ∀ {s₁ s₁' s₂ s₂'} → ∞ (♭ s₁ ∼ ♭ s₁') → ∞ (♭ s₂ ∼ ♭ s₂') → Case s₁ s₂ ∼ Case s₁' s₂'
    ∼-Semi : ∀ {s₁ s₁' s₂ s₂'} → ∞ (♭ s₁ ∼ ♭ s₁') → ∞ (♭ s₂ ∼ ♭ s₂') → Semi s₁ s₂ ∼ Semi s₁' s₂'
    ∼-Semi-Skip-Left-Left : ∀ {s₁ s₂ s₃} → ∞ (♭ s₁ ∼ Skip) → ∞ (♭ s₂ ∼ s₃) → Semi s₁ s₂ ∼ s₃
    -- ∼-Semi-Skip-Right-Left : ∀ {s₁ s₂ s₃} → ∞ (♭ s₂ ∼ Skip) → ∞ (♭ s₁ ∼ s₃) → Semi s₁ s₂ ∼ s₃
    -- ∼-Semi-Skip-Left-Right : ∀ {s₁ s₂ s₃} → ∞ (♭ s₁ ∼ Skip) → ∞ (♭ s₂ ∼ s₃) → s₃ ∼ Semi s₁ s₂
    -- ∼-Semi-Skip-Right-Right : ∀ {s₁ s₂ s₃} → ∞ (♭ s₂ ∼ Skip) → ∞ (♭ s₁ ∼ s₃) → s₃ ∼ Semi s₁ s₂
    ∼-Semi-Case-Left : ∀ {s₁ s₂ s₃ sl1 sl2 sr}
      → ∞ (♭ sl1 ∼ Semi s₁ s₃) → ∞ (♭ sl2 ∼ Semi s₂ s₃) → ∞ (♭ sr ∼ Case s₁ s₂) → Case sl1 sl2 ∼ Semi sr s₃
    ∼-Semi-Case-Right : ∀ {s₁ s₂ s₃ sl1 sl2 sr}
      → ∞ (♭ sl1 ∼ Semi s₁ s₃) → ∞ (♭ sl2 ∼ Semi s₂ s₃) → ∞ (♭ sr ∼ Case s₁ s₂) → Semi sr s₃ ∼ Case sl1 sl2

  -- reflexivity

  ∼-refl : (s : SType') → s ∼ s
  ∼-refl Skip = ∼-Skip
  ∼-refl (Semi x x₁) = ∼-Semi (♯ ∼-refl (♭ x)) (♯ ∼-refl (♭ x₁))
  ∼-refl (Case s₁ s₂) = ∼-Case (♯ ∼-refl (♭ s₁)) (♯ ∼-refl (♭ s₂))
  ∼-refl (c f)        = {!!}

  -- symmetry

  ∼-sym : ∀ {s₁ s₂} → s₁ ∼ s₂ → s₂ ∼ s₁
  ∼-sym ∼-Skip = ∼-Skip
  ∼-sym (∼-Case s₁' s₂') = ∼-Case (♯ ∼-sym (♭ s₁')) (♯ ∼-sym (♭ s₂'))
  ∼-sym (∼-Semi s₁' s₂') = ∼-Semi (♯ ∼-sym (♭ s₁')) (♯ ∼-sym (♭ s₂'))
  ∼-sym (∼-Semi-Skip-Left-Left s₁∼s₂ s₁∼s₃) = {!∼-Semi-Skip-Left-Right s₁∼s₂ s₁∼s₃!}
  -- ∼-sym (∼-Semi-Skip-Right-Left s₁∼s₂ s₁∼s₃) = ∼-Semi-Skip-Right-Right s₁∼s₂ s₁∼s₃
  -- ∼-sym (∼-Semi-Skip-Left-Right s₁∼s₂ s₁∼s₃) = ∼-Semi-Skip-Left-Left s₁∼s₂ s₁∼s₃
  -- ∼-sym (∼-Semi-Skip-Right-Right s₁∼s₂ s₁∼s₃) = ∼-Semi-Skip-Right-Left s₁∼s₂ s₁∼s₃
  ∼-sym (∼-Semi-Case-Left sl1 sl2 sr) = ∼-Semi-Case-Right sl1 sl2 sr
  ∼-sym (∼-Semi-Case-Right sl1 sl2 sr) = ∼-Semi-Case-Left sl1 sl2 sr


  -- transitivity

  ∼-trans : ∀ {s₁ s₂ s₃} → s₁ ∼ s₂ → s₂ ∼ s₃ → s₁ ∼ s₃
  ∼-trans ∼-Skip ∼-Skip = ∼-Skip
  -- ∼-trans ∼-Skip (∼-Semi-Skip-Left-Right x x₁) = ∼-Semi-Skip-Left-Right x x₁
  -- ∼-trans ∼-Skip (∼-Semi-Skip-Right-Right x x₁) = ∼-Semi-Skip-Right-Right x x₁
  ∼-trans (∼-Case x x₁) (∼-Case x₂ x₃) = ∼-Case (♯ ∼-trans (♭ x) (♭ x₂)) (♯ ∼-trans (♭ x₁) (♭ x₃))
  -- ∼-trans (∼-Case x x₁) (∼-Semi-Skip-Left-Right x₂ x₃) = ∼-Semi-Skip-Left-Right x₂ (♯ ∼-trans (♭ x₃) (∼-Case (♯ ∼-sym (♭ x)) (♯ ∼-sym (♭ x₁))))
  -- ∼-trans (∼-Case x x₁) (∼-Semi-Skip-Right-Right x₂ x₃) = ∼-Semi-Skip-Right-Right x₂ (♯ ∼-trans (♭ x₃) (∼-Case (♯ ∼-sym (♭ x)) (♯ ∼-sym (♭ x₁))))
  ∼-trans (∼-Case x x₁) (∼-Semi-Case-Left x₂ x₃ x₄) = ∼-Semi-Case-Left (♯ ∼-trans (♭ x) (♭ x₂)) (♯ ∼-trans (♭ x₁) (♭ x₃)) x₄
  ∼-trans (∼-Semi x x₁) (∼-Semi x₂ x₃) = ∼-Semi (♯ ∼-trans (♭ x) (♭ x₂)) (♯ ∼-trans (♭ x₁) (♭ x₃))
  ∼-trans (∼-Semi x x₁) (∼-Semi-Skip-Left-Left x₂ x₃) = ∼-Semi-Skip-Left-Left (♯ ∼-trans (♭ x) (♭ x₂)) (♯ ∼-trans (♭ x₁) (♭ x₃))
  -- ∼-trans (∼-Semi x x₁) (∼-Semi-Skip-Right-Left x₂ x₃) = ∼-Semi-Skip-Right-Left (♯ ∼-trans (♭ x₁) (♭ x₂)) (♯ ∼-trans (♭ x) (♭ x₃))
  -- ∼-trans (∼-Semi x x₁) (∼-Semi-Skip-Left-Right x₂ x₃) = ∼-Semi-Skip-Left-Right x₂ (♯ ∼-trans (♭ x₃) (∼-Semi (♯ ∼-sym (♭ x)) (♯ ∼-sym (♭ x₁))))
  -- ∼-trans (∼-Semi x x₁) (∼-Semi-Skip-Right-Right x₂ x₃) = ∼-Semi-Skip-Right-Right x₂ (♯ ∼-trans (♭ x₃) (∼-Semi (♯ ∼-sym (♭ x)) (♯ ∼-sym (♭ x₁))))
  ∼-trans (∼-Semi x x₁) (∼-Semi-Case-Right x₂ x₃ x₄) = ∼-Semi-Case-Right (♯ ∼-trans (♭ x₂) (∼-Semi (♯ ∼-refl _) (♯ ∼-sym (♭ x₁)))) (♯ ∼-trans (♭ x₃) (∼-Semi (♯ ∼-refl _) (♯ ∼-sym (♭ x₁)))) (♯ ∼-trans (♭ x) (♭ x₄))
  ∼-trans (∼-Semi-Skip-Left-Left x x₁) ∼-Skip = ∼-Semi-Skip-Left-Left x x₁
  ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Case x₂ x₃) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Case x₂ x₃))
  ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Semi x₂ x₃) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Semi x₂ x₃))
  ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Semi-Skip-Left-Left x₂ x₃) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Semi-Skip-Left-Left x₂ x₃))
  -- ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Semi-Skip-Right-Left x₂ x₃) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Semi-Skip-Right-Left x₂ x₃))
  -- ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Semi-Skip-Left-Right x₂ x₃) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Semi-Skip-Left-Right x₂ x₃))
  -- ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Semi-Skip-Right-Right x₂ x₃) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Semi-Skip-Right-Right x₂ x₃))
  ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Semi-Case-Left x₂ x₃ x₄) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Semi-Case-Left x₂ x₃ x₄))
  ∼-trans (∼-Semi-Skip-Left-Left x x₁) (∼-Semi-Case-Right x₂ x₃ x₄) = ∼-Semi-Skip-Left-Left x (♯ ∼-trans (♭ x₁) (∼-Semi-Case-Right x₂ x₃ x₄))
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) ∼-Skip = ∼-Semi-Skip-Right-Left x x₁
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Case x₂ x₃) = ∼-Semi-Skip-Right-Left x (♯ ∼-trans (♭ x₁) (∼-Case x₂ x₃))
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Semi x₂ x₃) = ∼-Semi-Skip-Right-Left x (♯ ∼-trans (♭ x₁) (∼-Semi x₂ x₃))
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Semi-Skip-Left-Left x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Semi-Skip-Right-Left x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Semi-Skip-Left-Right x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Semi-Skip-Right-Right x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Semi-Case-Left x₂ x₃ x₄) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Left x x₁) (∼-Semi-Case-Right x₂ x₃ x₄) = {!!}
  --∼-trans (∼-Semi-Skip-Left-Right x x₁) (∼-Semi x₂ x₃) = ∼-Semi-Skip-Left-Right (♯ ∼-trans (∼-sym (♭ x₂)) (♭ x)) (♯ ∼-trans (∼-sym (♭ x₃)) (♭ x₁))
  -- ∼-trans (∼-Semi-Skip-Left-Right x x₁) (∼-Semi-Skip-Left-Left x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Left-Right x x₁) (∼-Semi-Skip-Right-Left x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Left-Right x x₁) (∼-Semi-Skip-Left-Right x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Left-Right x x₁) (∼-Semi-Skip-Right-Right x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Left-Right x x₁) (∼-Semi-Case-Right x₂ x₃ x₄) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Right x x₁) (∼-Semi x₂ x₃) = ∼-Semi-Skip-Right-Right (♯ ∼-trans (∼-sym (♭ x₃)) (♭ x)) (♯ ∼-trans (∼-sym (♭ x₂)) (♭ x₁))
  -- ∼-trans (∼-Semi-Skip-Right-Right x x₁) (∼-Semi-Skip-Left-Left x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Right x x₁) (∼-Semi-Skip-Right-Left x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Right x x₁) (∼-Semi-Skip-Left-Right x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Right x x₁) (∼-Semi-Skip-Right-Right x₂ x₃) = {!!}
  -- ∼-trans (∼-Semi-Skip-Right-Right x x₁) (∼-Semi-Case-Right x₂ x₃ x₄) = {!!}
  ∼-trans (∼-Semi-Case-Left x x₁ x₂) (∼-Semi x₃ x₄) = ∼-Semi-Case-Left {!!} (♯ ∼-trans (♭ x₁) (∼-Semi (♯ ∼-refl _) x₄)) (♯ ∼-trans (∼-sym (♭ x₃)) (♭ x₂))
  ∼-trans (∼-Semi-Case-Left x x₁ x₂) (∼-Semi-Skip-Left-Left x₃ x₄) = {!!}
  -- ∼-trans (∼-Semi-Case-Left x x₁ x₂) (∼-Semi-Skip-Right-Left x₃ x₄) = {!!}
  -- ∼-trans (∼-Semi-Case-Left x x₁ x₂) (∼-Semi-Skip-Left-Right x₃ x₄) = {!!}
  -- ∼-trans (∼-Semi-Case-Left x x₁ x₂) (∼-Semi-Skip-Right-Right x₃ x₄) = {!!}
  ∼-trans (∼-Semi-Case-Left x x₁ x₂) (∼-Semi-Case-Right x₃ x₄ x₅) = {!!}
  ∼-trans (∼-Semi-Case-Right x x₁ x₂) (∼-Case x₃ x₄) = ∼-Semi-Case-Right (♯ ∼-trans (∼-sym (♭ x₃)) (♭ x)) (♯ ∼-trans (∼-sym (♭ x₄)) (♭ x₁)) x₂
  -- ∼-trans (∼-Semi-Case-Right x x₁ x₂) (∼-Semi-Skip-Left-Right x₃ x₄) = {!!}
  -- ∼-trans (∼-Semi-Case-Right x x₁ x₂) (∼-Semi-Skip-Right-Right x₃ x₄) = {!!}
  ∼-trans (∼-Semi-Case-Right x x₁ x₂) (∼-Semi-Case-Left x₃ x₄ x₅) = {!!}
