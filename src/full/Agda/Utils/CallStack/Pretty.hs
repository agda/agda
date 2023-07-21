module Agda.Utils.CallStack.Pretty
  ( -- This module only exports instances.
  ) where

import Agda.Utils.CallStack.Base
  ( CallSite
  , CallStack
  , SrcLoc(..)
  , getCallStack
  )
import Agda.Syntax.Common.Pretty
  ( (<+>), ($+$), (<>)
  , pshow, text
  , colon, comma
  , nest, parens
  , hcat, hsep, vcat
  , Pretty(pretty)
  )

instance Pretty SrcLoc where
  pretty SrcLoc {..} = hsep [physicalLoc, "in", logicalLoc]
      where
        physicalLoc = hcat [text srcLocFile, colon, pshow srcLocStartLine, colon, pshow srcLocStartCol]
        logicalLoc = hcat [text srcLocPackage, colon, text srcLocModule]

instance Pretty CallSite where
  pretty (fun, loc) = hsep [text fun <> comma, "called at", pretty loc]

instance Pretty CallStack where
  pretty cs = case fmap pretty (getCallStack cs) of
    []                  -> parens "empty CallStack"
    firstLoc : restLocs -> firstLoc $+$ nest 2 (vcat restLocs)
