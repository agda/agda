{-# OPTIONS --without-K --safe --no-universe-polymorphism --sized-types
            --no-guardedness --no-subtyping #-}

module Agda.Builtin.Size where

{-# BUILTIN SIZEUNIV SizeU #-}
{-# BUILTIN SIZE     Size   #-}
{-# BUILTIN SIZELT   Size<_ #-}
{-# BUILTIN SIZESUC  ↑_     #-}
{-# BUILTIN SIZEINF  ∞      #-}
{-# BUILTIN SIZEMAX  _⊔ˢ_  #-}

{-# FOREIGN GHC
  type SizeLT i = ()
  #-}

{-# COMPILE GHC Size   = type ()     #-}
{-# COMPILE GHC Size<_ = type SizeLT #-}
{-# COMPILE GHC ↑_     = \_ -> ()    #-}
{-# COMPILE GHC ∞      = ()          #-}
{-# COMPILE GHC _⊔ˢ_   = \_ _ -> ()  #-}
