module Issue6962SignatureRHSParseError where

-- The original LHS action rejects an invalid head before a malformed type.
bad (λ x → x) : ) Set
