module SafeFlagPrimTrustMe where

-- Cannot make an example with the correct type signature for
-- primTrustMe since it requires postulated universe level builtins,
-- which --safe flag will reject.

private
 primitive
   primTrustMe : Set
