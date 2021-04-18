{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Only instances exported
module Agda.TypeChecking.Serialise.Instances () where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Highlighting ()
import Agda.TypeChecking.Serialise.Instances.Errors ()

instance EmbPrj Interface where
  icod_ (Interface a b c d e f g h i j k l m n o p q r s t) =
    icodeN' Interface a b c d e f g h i j k l m n o p q r s t

  value = vcase valu where
    valu [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] =
      valuN Interface a b c d e f g h i j k l m n o p q r s t
    valu _ = malformed
