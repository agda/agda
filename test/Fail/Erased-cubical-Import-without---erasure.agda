{-# OPTIONS --erased-cubical #-}

-- Modules that use --cubical can be imported when --erased-cubical is
-- used.

open import Erased-cubical-Import.Cubical

-- However, names from such modules cannot be used unless
-- --erasure is active.

_ : {A : Set} → A → ∥ A ∥
_ = ∣_∣
