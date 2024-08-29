-- Andreas, 2024-08-29
-- Trigger error "Binding syntax is not allowed in idiom brackets"

postulate
  F     : Set → Set
  pure  : ∀ {A} → A → F A
  _<*>_ : ∀ {A B} → F (A → B) → F A → F B

  bind  : ∀ {A B} → F A → (A → F B) → F B

syntax bind m (λ x → k) = x ← m then k

_ = (| _ ← _ then _ |)

-- Expected error:
-- Binding syntax is not allowed in idiom brackets
