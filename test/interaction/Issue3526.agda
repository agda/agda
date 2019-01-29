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
