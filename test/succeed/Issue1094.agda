-- 2014-04-06 Andreas, issue reported by flickyfrans
-- {-# OPTIONS --show-implicit -v tc.section.apply:60 #-}

open import Common.Level renaming (lsuc to suc)

record RawMonad {α β : Level} (M : {γ : Level} → Set γ → Set γ) : Set (suc (α ⊔ β)) where
  infixl 1 _>>=_
  field
    return' : {A : Set α} → A → M A
    _>>=_   : {A : Set α} {B : Set β} → M A → (A → M B) → M B

module MonoMonad {α} = RawMonad {α} {α}
module MM = MonoMonad {{...}}

-- return : {α : Level} {M : {γ : Level} → Set γ → Set γ} {{m : RawMonad {α} {α} M }} {A : Set α} → A → M A

return : _
return = MM.return'

-- WAS: Panic: deBruijn index out of scope: 2 in context [M,α]
-- when checking that the expression MM.return' has type _15

-- CAUSE: Ill-formed section telescope produced by checkSectionApplication.

-- NOW: Works.
