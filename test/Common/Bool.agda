module Common.Bool where

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA_UHC Bool __BOOL__ __TRUE__ __FALSE__ #-}
{-# COMPILED_JS Bool function (x,v) { return (x? v["true"](): v["false"]()); } #-}
{-# COMPILED_JS true true #-}
{-# COMPILED_JS false false #-}

not : Bool -> Bool
not true  = false
not false = true

notnot : Bool -> Bool
notnot true  = not (not true)
notnot false = not (not false)

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

