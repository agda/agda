{-# OPTIONS --erased-cubical --erasure #-}

-- Modules that use --cubical can be imported when --erased-cubical is
-- used.

open import Erased-cubical-Import.Cubical

-- However, definitions from such modules can only be used in erased
-- contexts.

_ : {A : Set} → A → ∥ A ∥
_ = ∣_∣
