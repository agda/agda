module Issue6962InvalidClauseHead where

-- Moving head classification must preserve the pattern error and its range.
bad (λ x → x) = Set
