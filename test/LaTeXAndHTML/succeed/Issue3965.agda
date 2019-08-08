open import Agda.Builtin.Nat

f : Nat → Nat
f 0 = zero
f 0 = 0        -- All                      -- But Only
f (suc n) = n  -- These
f 0 = 0        -- Lines                    -- These Two
               -- Used to be highlighted   -- Should be!


g : Nat → Nat
g 0 = zero
g 0     -- The highlihting should still
  = 0   -- span multiple lines if the clause does
g (suc n) = n
g 0     -- Even
        -- With
        -- A Lot
   = 0  -- Of Empty Lines in between

