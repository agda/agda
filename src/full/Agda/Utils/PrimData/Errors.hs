
{-# LANGUAGE RankNTypes, KindSignatures, PolyKinds #-}

module Agda.Utils.PrimData.Errors where

import GHC.Stack
import GHC.Exts

undefElem :: forall r (a :: TYPE r). HasCallStack => a
undefElem = error "undefined element"
{-# NOINLINE undefElem #-}

unpinnedContents :: forall r (a :: TYPE r). HasCallStack => a
unpinnedContents = error "Data.Array.FM: can't take contents of unpinned array"
{-# NOINLINE unpinnedContents #-}
