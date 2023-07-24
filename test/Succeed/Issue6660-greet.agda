-- Lawrence, Andreas, 2023-06-12, issue #6660
-- Inlining constructor _>>=_ activated after first use in _>>_
-- to facilitate inlining of auxiliary function _>>_.

{-# OPTIONS --guardedness #-}
{-# OPTIONS --exact-split #-}
{-# OPTIONS -WnoInlineNoExactSplit #-}

open import Agda.Builtin.String
open import Agda.Builtin.Unit

data Cmd : Set where
    put-str-ln : String → Cmd
    get-str-ln : Cmd

cmd-ret-ty : Cmd → Set
cmd-ret-ty (put-str-ln _) = ⊤
cmd-ret-ty get-str-ln = String

record ITree : Set where
    coinductive; constructor _>>=_
    field head : Cmd
    field tail : cmd-ret-ty head → ITree
open ITree

_>>_ : Cmd → ITree → ITree
c >> t = c >>= λ _ → t

-- This must go after the definition of _>>_
-- so that _>>_ is not turned into a definition copattern matching
-- and thus _>>_ can be inlined.
{-# INLINE _>>=_ #-}

{-# INLINE _>>_ #-}

greet : ITree
greet = do
    put-str-ln "Who are you?"
    name ← get-str-ln
    put-str-ln (primStringAppend "Hello, " name)
    greet
