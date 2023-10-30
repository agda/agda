{-# OPTIONS --cubical-compatible --no-universe-polymorphism --sized-types
            --no-guardedness --level-universe #-}

module Agda.Builtin.Size where

{-# BUILTIN SIZEUNIV SizeUniv #-}
{-# BUILTIN SIZE     Size     #-}
{-# BUILTIN SIZELT   Size<_   #-}
{-# BUILTIN SIZESUC  ↑_       #-}
{-# BUILTIN SIZEINF  ∞        #-}
{-# BUILTIN SIZEMAX  _⊔ˢ_     #-}

{-# COMPILE GHC Size   = type ()     #-}
{-# COMPILE GHC Size<_ = type ()     #-}
{-# COMPILE GHC ↑_     = \_ -> ()    #-}
{-# COMPILE GHC ∞      = ()          #-}
{-# COMPILE GHC _⊔ˢ_   = \_ _ -> ()  #-}
