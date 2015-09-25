-- This was accepted, since we didn't fail on mismatched sorts when
-- comparing types.
module Issue485 where

ap : ((A : Set) → A → A) → Set → Set
ap f A = f _ A
