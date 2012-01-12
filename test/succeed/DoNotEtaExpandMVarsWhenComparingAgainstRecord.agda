-- 2010-10-15

module DoNotEtaExpandMVarsWhenComparingAgainstRecord where

open import Common.Irrelevance  

data _==_ {A : Set1}(a : A) : A -> Set where
  refl : a == a

record IR : Set1 where
  constructor mkIR
  field
    .fromIR : Set

open IR

reflIR2 : (r : IR) -> _ == mkIR (fromIR r)
reflIR2 r = refl {a = _}
-- this would fail if 
-- ? = mkIR (fromIR r)
-- would be solved by
-- mkIR ?1 = mkIR (fromIR r)
-- because then no constraint is generated for ?1 due to triviality
