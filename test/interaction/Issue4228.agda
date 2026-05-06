-- Andreas, 2026-05-05, issue #4228
-- Solved interaction points should not depend on genTel after generalization.

-- {-# OPTIONS -v tc.generalize:30 #-}

postulate
  F : Set → Set
  P : (A : Set) → F A → Set
  f : (A : Set) → F A

variable
  A : Set

postulate
  p : P {!!} (f A)   -- C-c C-,

-- WAS:
-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- genTel : Issue3656.GeneralizeTel   (not in scope)

-- NOW:
-- Goal: Set
-- ———— Context ———————————————————————————————————————————————
-- A : Set

---------------------------------------------------------------------------
-- The issue was reported again as #5851.

interleaved mutual

  data Scope : Set
  variable sc : Scope

  data Decls (sc : Scope) : Set
  variable ds : Decls sc

  data Block (sc : Scope) : Set where
    bDecls : (ds : Decls sc) → Block sc

  data Scope where
    _▷_ : (sc : Scope) (b : Block sc) → Scope

  data Decl (sc : Scope) : Set where
  variable d : Decl sc

  data Decls where
    _▷_ : (ds : Decls sc) (d : Decl (sc ▷ bDecls ds)) → Decls sc

  data Deco (topScope : Scope) : Decls sc → Set where
    _▷[_] : Deco topScope {sc} ds
          → (d : Decl (sc ▷ bDecls ds))
          → Deco topScope (ds ▷ d)
  variable deco : Deco sc ds

  data DName : (sc : Scope) → Decl sc → Set where

  data MName (sc : Scope) : Deco sc ds  → Set where
    here  : ∀{d : Decl (sc ▷ bDecls ds)}
          → DName (sc ▷ bDecls {! !}) d    -- C-c C-,  and  C-c C-=
          → MName sc (deco ▷[ d  ])

-- WAS:
-- Goal: Decls sc
-- ————————————————————————————————————
-- d      : Decl (sc ▷ bDecls ds)
-- genTel : bug-genTel.GeneralizeTel sc   (not in scope)
-- sc     : Scope

-- NOW:
-- Goal: Decls sc
-- ———— Context ———————————————————————————————————————————————
-- d    : Decl (sc ▷ bDecls ds)
-- deco : Deco sc ds
-- ds   : Decls sc
-- sc   : Scope
