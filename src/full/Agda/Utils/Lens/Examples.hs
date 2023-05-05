-- | Examples how to use "Agda.Utils.Lens".

module Agda.Utils.Lens.Examples where

import Agda.Utils.Functor
import Agda.Utils.Lens

data Record a b = Record
  { field1 :: a
  , field2 :: b
  }

-- | (View source:) This is how you implement a lens for a record field.
lensField1 :: Lens' (Record a b) a
lensField1 f r = f (field1 r) <&> \ a -> r { field1 = a }

lensField2 :: Lens' (Record a b) b
lensField2 f r = f (field2 r) <&> \ b -> r { field2 = b }
