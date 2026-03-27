
module Issue8483 where

open import Agda.Builtin.String

postulate
  HTMLInputElement : Set
  HTMLTextAreaElement : Set
  IO : Set → Set

-- local modules to avoid name clashes on 'get-value':

module HTMLInputElement where
  postulate get-value : HTMLInputElement → IO String
  {-# COMPILE JS get-value = e => ks => ks(e.value) #-}

module HTMLTextAreaElement where
  postulate get-value : HTMLTextAreaElement → IO String
  {-# COMPILE JS get-value = e => ks => ks(e.value) #-}

