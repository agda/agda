module AnonymousRecConstrCopy3b where

import AnonymousRecConstrCopy3a as Orig
open Orig Set

_ : Orig.Bar Set
_ = Bar.constructor
