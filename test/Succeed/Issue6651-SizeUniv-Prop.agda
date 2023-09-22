-- Andreas, 2023-05-19, issue #6651
-- SizeUniv can be a predecessor of Setω

{-# OPTIONS --sized-types #-}
{-# OPTIONS --prop #-}  -- should also work with Prop on

open import Agda.Primitive
open import Agda.Builtin.Size

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

S-U : Setω
S-U = _ -- should solve to SizeUniv
        -- Error WAS: univSort _3 != Setω

S : S-U
S = _   -- should solve to Size

foo : S → S
foo i = ∞

mutual-block = END
