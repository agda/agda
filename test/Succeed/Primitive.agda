-- Andreas, 2023-05-08, test loading all the primitive/builtin modules

-- We need some options to satisfy infective features.
-- Currently --cubical --with-K is supported, enabling us to import all builtin modules.

{-# OPTIONS --cubical     #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting   #-}
{-# OPTIONS --sized-types #-}
{-# OPTIONS --with-K      #-}

import Agda.Primitive
import Agda.Primitive.Cubical

import Agda.Builtin.Bool
import Agda.Builtin.Char
import Agda.Builtin.Char.Properties
import Agda.Builtin.Coinduction
import Agda.Builtin.Cubical.Equiv
import Agda.Builtin.Cubical.Glue
import Agda.Builtin.Cubical.HCompU
import Agda.Builtin.Cubical.Id
import Agda.Builtin.Cubical.Path
import Agda.Builtin.Cubical.Sub
import Agda.Builtin.Equality
import Agda.Builtin.Equality.Erase
import Agda.Builtin.Equality.Rewrite
import Agda.Builtin.Float
import Agda.Builtin.Float.Properties
import Agda.Builtin.FromNat
import Agda.Builtin.FromNeg
import Agda.Builtin.FromString
import Agda.Builtin.IO
import Agda.Builtin.Int
import Agda.Builtin.List
import Agda.Builtin.Maybe
import Agda.Builtin.Nat
import Agda.Builtin.Reflection
import Agda.Builtin.Reflection.External
import Agda.Builtin.Reflection.Properties
import Agda.Builtin.Sigma
import Agda.Builtin.Size
import Agda.Builtin.Strict
import Agda.Builtin.String
import Agda.Builtin.String.Properties
import Agda.Builtin.TrustMe
import Agda.Builtin.Unit
import Agda.Builtin.Word
import Agda.Builtin.Word.Properties
