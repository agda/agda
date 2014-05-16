-- {-# OPTIONS -v tc.with:40 #-}

id : (A : Set) → A → A
id A = {!id′!}
 -- C-c C-h produces:       id′ : ∀ {A} → A
 -- when it should produce: id′ : ∀ {A} → A → A
