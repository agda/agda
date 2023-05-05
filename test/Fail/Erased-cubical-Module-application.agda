{-# OPTIONS --erased-cubical --erasure #-}

-- Modules that use --cubical can be imported when --erased-cubical is
-- used.

import Erased-cubical-Module-application.Cubical
module EC = Erased-cubical-Module-application.Cubical Set

-- However, definitions from such modules can only be used in erased
-- contexts.

_ : {A : Set} → A → EC.∥ A ∥
_ = EC.∣_∣
