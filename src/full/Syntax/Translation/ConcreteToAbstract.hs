{-# OPTIONS -fglasgow-exts #-}

{-| Translation from "Syntax.Concrete" to "Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Syntax.Translation.ConcreteToAbstract where

import Syntax.Concrete as C
import Syntax.Abstract as A
import Syntax.Position
import Syntax.Common
import Syntax.Explanation
--import Syntax.Interface
--import Syntax.Concrete.Definitions
--import Syntax.Concrete.Fixity
import Syntax.Scope



