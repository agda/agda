
------------------------------------------------------------------------
-- | Code for instructing Emacs to do things
------------------------------------------------------------------------

module Agda.Interaction.EmacsCommand
  ( displayInfo
  , clearRunningInfo
  , displayRunningInfo
  ) where

import Prelude hiding (null)

import Data.Bifunctor (second)
import Data.Text qualified as Text

import Agda.Syntax.Common.Pretty           (DocTree)

import Agda.Interaction.Emacs.Lisp
import Agda.Interaction.Highlighting.Emacs (HighlightingInfo, lispifyHighlightingInfo_)

import Agda.TypeChecking.Monad.Base.Types  (ModuleToSource)

import Agda.Utils.Null
import Agda.Utils.String                   (quote)
import Agda.Utils.DocTree                  (treeToTextNoAnn, treeToTextWithAnn)

-- | @displayInfo header content append m@ displays @content@
-- with header @header@ in some suitable way in the Agda information buffer.
-- If @append@ is @True@, then the content is appended to previous content
-- (if any), otherwise any previous content is deleted.
-- If @m@ is @Just 'ModuleToSource'@ then @content@ is rendered with annotations,
-- otherwise annotations in @content@ are discarded and just the text is displayed.

displayInfo :: String -> DocTree -> Bool -> Maybe ModuleToSource -> Lisp String
displayInfo header content append m = L $ concat
  [ [ A "agda2-info-action"
    , A (quote header)
    , A (quote $ Text.unpack t)
    , A (if append then "t" else "nil")
    ]
  , map Q ann
  ]
  where
    (t, ann) = case m of
      Nothing  -> (, [])                                $ treeToTextNoAnn   content
      Just m2s -> second (lispifyHighlightingInfo_ m2s) $ treeToTextWithAnn content

------------------------------------------------------------------------
-- Running info

-- | Header to display in the Agda information buffer for "running info".

runningInfoHeader :: String
runningInfoHeader = "*Type-checking*"

-- | Clear the running info buffer.

clearRunningInfo :: Lisp String
clearRunningInfo = displayInfo runningInfoHeader empty False Nothing

-- | Display running information about what the type-checker is up to.

displayRunningInfo :: DocTree -> Maybe ModuleToSource -> Lisp String
displayRunningInfo t = displayInfo runningInfoHeader t True
