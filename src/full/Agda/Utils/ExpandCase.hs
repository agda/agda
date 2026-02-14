
{- |
This module is intended for high-performance programming. Concretely, the 'ExpandCase' class can be
used to force GHC to avoid compiling 'Reader', 'Endo' or 'State'-based code to unnecessary closures.
You can observe its usage in 'Agda.TypeChecking.Free.Generic'. For a smaller example and some
explanation, consider the following.

@
f :: Bool -> Endo Int
f b = case b of
  True  -> mempty
  False -> Endo (+ 10)
@

The desired @-O1@ output should be the following (ignoring newtype casts):

@
f = \b n -> case b of
  True  -> n
  False -> n + 10
@

A typical undesired output would be

@
f = \b -> case b of
  True  -> \n -> n
  False -> \n -> n + 10
@

Returning closures can be better or worse, depending on the program context. However, in
high-performance situations we almost never want to return closures, and GHC is not nearly reliable
enough at getting rid of the closures.

Using 'ExpandCase', we can write code as follows.

@
f :: Bool -> Endo Int
f b = expand \ret -> case b of
  True  -> ret mempty
  False -> ret $ Endo (+10)
@

Here, 'expand' immediately introduces a lambda abstraction, and the @ret@ continuation applies the
"body" of the definition to the freshly abstracted variable. Hence, we get something like the
following as an intermediate piece of Core:

@
f :: Bool -> Endo Int
f b = Endo \n -> case b of
  True  -> appEndo mempty n
  False -> appEndo (Endo (+10)) n
@

which is then reliably optimized to

@
f :: Bool -> Endo Int
f b = Endo \n -> case b of
  True  -> n
  False -> n + 10
@

NOTE: if you want to use this module, it is very strongly recommended that you check the Core of
your code!
-}

module Agda.Utils.ExpandCase where

import Data.Monoid
import GHC.Exts (oneShot)

class ExpandCase a where
  type Result a
  expand :: ((a -> Result a) -> Result a) -> a

instance ExpandCase Any where
  type Result Any = Any
  expand k = k id; {-# INLINE expand #-}

instance ExpandCase All where
  type Result All = All
  expand k = k id; {-# INLINE expand #-}

instance ExpandCase (Endo a) where
  type Result (Endo a) = a
  {-# INLINE expand #-}
  expand k = Endo (oneShot \a -> k (oneShot \act -> appEndo act a))
