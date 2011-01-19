-- Note: It would be good if the code below type checked, this file
-- documents that it doesn't.

module Issue151b where

record A : Set₁ where
  field
    El : Set

postulate
  D : A → Set
  d : (a : A) → D a
  test : (a : A) → _

-- The following definition generates a constraint
--   α record{ El = A.El a } == D a
-- on the metavariable above. To solve this the constraint
-- solver has to eta contract the record to see that the
-- left hand side is a proper Miller pattern.
bar : (a : A) → D a
bar a = test record{ El = A.El a }
