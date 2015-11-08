
module Issue616 where

open import Common.Coinduction

const : ∀ {a b}{A : Set a}{B : Set b} → A → B → A
const x _ = x

-- The recursive call should be ignored by the termination checker,
-- since ♭ is a projection function and shouldn't store its implicit
-- arguments.
contrived : Set₁
contrived = ♭ {A = const _ contrived} (♯ Set)
