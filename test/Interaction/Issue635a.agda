-- {-# OPTIONS -v interaction.case:20 -v tc.cover:20 #-}
-- Andreas, 2015-05-29, issue reported by Stevan Andjelkovic

record Cont : Set₁ where
  constructor _◃_
  field
    Sh  : Set
    Pos : Sh → Set

open Cont

data W (C : Cont) : Set where
  sup : (s : Sh C) (k : Pos C s → W C) → W C

-- If I case split on w:
bogus : {C : Cont} → W C → Set
bogus w = {!w!}

-- WAS internally :  bogus {Sh ◃ Pos} w = ?
-- WAS after split:  bogus {Sh ◃ Pos} (sup s k) = ?
-- NOW internally :  bogus {_} w = ?
-- NOW as expected:  bogus (sup s k) = ?
