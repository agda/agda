{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Only instances exported
module Agda.TypeChecking.Serialise.Instances () where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Abstract ()
import Agda.TypeChecking.Serialise.Instances.Common ()
import Agda.TypeChecking.Serialise.Instances.Compilers ()
import Agda.TypeChecking.Serialise.Instances.Highlighting ()
import Agda.TypeChecking.Serialise.Instances.Internal ()
import Agda.TypeChecking.Serialise.Instances.Errors ()

instance EmbPrj Interface where
  icod_ (Interface a b c d e f g h i j k l m n o p q) =
    icodeN' Interface a b c d e f g h i j k l m n o p q

  value = vcase valu where
    valu [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q] =
      valuN Interface a b c d e f g h i j k l m n o p q
    valu _ = malformed
