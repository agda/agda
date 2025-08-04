
------------------------------------------------------------------------
-- | Code for instructing Emacs to do things
------------------------------------------------------------------------

module Agda.Interaction.EmacsCommand
  ( displayInfo
  , clearRunningInfo
  , displayRunningInfo
  ) where

import Agda.Interaction.Emacs.Lisp
import Agda.Interaction.Highlighting.Emacs (HighlightingInfo, lispifyHighlightingInfo_)
import Agda.TypeChecking.Monad.Base.Types  (ModuleToSource)
import Agda.Utils.String                   (quote)

-- | @displayInfo append header content@ displays @content@
-- (with header @header@) in some suitable way in the Agda information buffer.
-- If @append@ is @True@, then the content is appended to previous content
-- (if any), otherwise any previous content is deleted.

displayInfo :: Bool -> String -> String -> Lisp String
displayInfo append header content =
    L [ A "agda2-info-action"
      , A (quote header)
      , A (quote content)
      , A (if append then "t" else "nil")
      ]

------------------------------------------------------------------------
-- Running info

-- | Header to display in the Agda information buffer for "running info".

runningInfoHeader :: String
runningInfoHeader = "*Type-checking*"

-- | Clear the running info buffer.

clearRunningInfo :: Lisp String
clearRunningInfo =
    displayInfo False runningInfoHeader ""

-- | Display running information about what the type-checker is up to.

displayRunningInfo :: String -> Lisp String
displayRunningInfo s =
    displayInfo True runningInfoHeader s
