-- Andreas, 2015-05-06, issue reported by Nisse

postulate
  _ : Set

postulate
  _ : Set

-- Error message WAS: "Multiple definitions of _."
-- BUT: If the first occurrence of _ is accepted, then the second one
-- should also be accepted.

-- Error NOW: "Invalid name: _"
