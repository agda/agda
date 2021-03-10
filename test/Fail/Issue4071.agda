
postulate
  List      : Set
  List-like : Set → Set

instance
  postulate
    List-is-list-like : List-like List

postulate
  to-List : ∀ {F : Set} ⦃ list-like : ∀ {X : Set} → List-like F ⦄ → F → List
  F       : Set

f : ⦃ list-like : List-like F ⦄ → List
f = to-List _
