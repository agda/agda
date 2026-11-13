module Issue6962ClauseRHSParseError where

-- Parse the complete declaration before validating duplicate parameters.
bad (A A : Set) = ) Set
