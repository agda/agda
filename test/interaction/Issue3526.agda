open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

idTrue : ∀ b → b ≡ true → Bool
idTrue b eq = {!!}

-- C-c C-c b RET gives us:
-- idTrue false eq = {!!}
-- idTrue true eq = {!!}

-- Now that we can leave `idTrue false eq` out because it's
-- trivially an impossible clause, it'd be nice to only get:
-- idTrue true eq = {!!}


-- But we should still get an absurd clause when we explictly
-- ask for it as in the following example:
-- C-c C-c e RET should give use
-- absurd ()

data Empty : Set where

absurd : ∀ {a} {A : Set a} → Empty → A
absurd e = {!!}

-- Similarly, C-C C-c b eq RET should give us
-- idTrue' false ()
-- idTrue' true refl = {!!}

idTrue' : ∀ b → b ≡ true → Bool
idTrue' b eq = {!!}

-- If the demanded split leads to trivially absurd clauses but the
-- function has a single clause, then we need to generate at least
-- one clause.

-- Therefore C-c C-c e RET should give us:
-- both .true refl f = {!!}

both : ∀ b → b ≡ true → b ≡ false → Bool
both b e f = {!!}

-- This should still be true in an already specialised context

both' : ∀ (c : Bool) b → b ≡ true → b ≡ false → Bool
both' false b e f = {!!}
both' true  b e f = {!!}
