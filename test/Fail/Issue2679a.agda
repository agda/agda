postulate
  A : Set

data B (a : A) : Set where
  conB : B a → B a → B a

data C (a : A) : B a → Set where
  conC : {bl br : B a} → C a bl → C a br → C a (conB bl br)

-- First bug.
{-
a !=<
"An internal error has occurred. Please report this as a bug.\nLocation of the error: src/full/Agda/TypeChecking/Telescope.hs:68\n"
of type A
when checking that the type
(a : A) (b : B a) (tl : C a (_16 a b)) →
C a (_16 a b) → (tr : C a (_17 a b)) → Set
of the generated with function is well-formed
-- Is there a contained error printing bug?
-}
goo : (a : A) (b : B a) (c : C a _) → Set
                                 -- giving b for _ resolves the error
goo a b (conC tl tr) with tl
... | _ = _
