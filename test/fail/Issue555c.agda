module Issue555c where

import Common.Level

record R {a} (A : Set a) : Set

record R A where
  field f : A