-- Andreas, 2015-03-10, issue reported by Andrea Vezzosi

postulate
  X : Set

data D p : X → Set p where
  c : ∀ i → D _ i

-- WAS: internal error in Substitute.hs due to negative De Bruijn index

-- should work now
