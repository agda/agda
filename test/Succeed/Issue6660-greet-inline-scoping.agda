-- Lawrence, 2023-06-19, issue #6660
-- Advanced test of INLINE scoping

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.String
open import Agda.Builtin.Unit

module _ where

    module Lib where
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
        open ITree public
        {-# INLINE _>>=_ #-}

        {-# NOINLINE _>>=_ #-}
        _>>_ : Cmd → ITree → ITree
        c >> t = c >>= λ _ → t
        {-# INLINE _>>=_ #-}

        {-# INLINE _>>_ #-}

    open Lib

    greet : ITree
    greet = do
        put-str-ln "Who are you?"
        name ← get-str-ln
        put-str-ln (primStringAppend "Hello, " name)
        greet
