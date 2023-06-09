{-# OPTIONS --guardedness #-}

open import Agda.Builtin.String
open import Agda.Builtin.Unit

data Cmd : Set where
    put-str-ln : String → Cmd
    get-str-ln : Cmd

cmd-ret-ty : Cmd → Set
cmd-ret-ty (put-str-ln _) = ⊤
cmd-ret-ty get-str-ln = String

record ITree : Set where
    coinductive
    field head : Cmd
    field tail : (cmd-ret-ty head) → ITree
open ITree

_>>=_ : (head : Cmd) → (cmd-ret-ty head → ITree) → ITree
(c >>= t) .head = c
(c >>= t) .tail = t
{-# INLINE _>>=_ #-}

_>>_ : Cmd → ITree → ITree
c >> t = c >>= λ _ → t
{-# INLINE _>>_ #-}

greet = do
    put-str-ln "Who are you?"
    name ← get-str-ln
    put-str-ln (primStringAppend "Hello, " name)
    greet
