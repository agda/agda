module _ where

import Agda.Primitive.Cubical as C


-- Cannot alias module exporting primitives with typechecking constraints.
module M = C
