-- Andreas, 2012-06-01, issue reported by fredrik.forsberg
module Issue661 where

import Common.Level

data Top : Set where
  tt : Top

mutual
  data Ctxt  : Set1 where
    [] : Ctxt
    cons : (G : Ctxt) -> (Env G -> Set) -> Ctxt

  Env : Ctxt -> Set --only important that Env x doesn't reduce for x neutral
  Env [] = Top
  Env (cons G A) = Top


module M (dummy : Set1) where

  data Uni (G : Ctxt) : Set1 where
    empty : Uni G
    sig : (A : Env G -> Set) -> Uni (cons G A) -> Uni G

open M Set

-- This example needs special constructor application checking
-- which propagates the parameters in.

c : Uni []
c = sig (\ _ -> Top) (sig (\ { tt -> Top}) empty)


-- Types:
-- empty : Uni _18
-- sig   : (A : Env _15 → Set) → Uni (cons _15 A) → Uni _15

--  c = sig (\ _ → Top) ?2  with ?2 : Uni (cons [] (λ _ → Top))
--  ?2 := sig ?3 ?4  with
--  ?3 : Env (cons [] (λ _ → Top)) → Set
--  ?4 : Uni (cons (cons [] (λ _ → Top)) ?3)

-- Error was:
-- Type mismatch
-- when checking that the pattern tt has type Env _14

