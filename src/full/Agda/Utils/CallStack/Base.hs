{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Utils.CallStack.Base (
  -- * Simple type aliases
    SrcLocPackage
  , SrcLocModule
  , SrcFun
  , SrcLocFile
  , SrcLocLine
  , SrcLocCol
  , CallSite
  , CallSiteFilter

  -- * String-based "pretty" representations
  , prettySrcLoc
  , prettyCallSite
  , prettyCallStack

  -- * Generic utilities over CallStack and CallSite
  , filterCallStack
  , headCallSite
  , overCallSites
  , popnCallStack
  , truncatedCallStack
  , withCallerCallStack
  , withCurrentCallStack
  , withNBackCallStack

  -- * Re-exported stuff
  , CallStack
  , callStack
  , fromCallSiteList
  , getCallStack
  , HasCallStack
  , SrcLoc(..)
  )
  where

import Data.List ( intercalate )
import Data.Maybe ( listToMaybe )
import GHC.Stack
  ( callStack
  , CallStack
  , emptyCallStack
  , fromCallSiteList
  , getCallStack
  , HasCallStack
  , popCallStack
  , prettySrcLoc
  , SrcLoc(..)
  )

-- * Type aliases

-- | Type of the package name of a @SrcLoc@
-- | e.g. `Agda-2.…`
type SrcLocPackage = String

-- | Type of the module name of a @SrcLoc@
-- | e.g. `Agda.Utils.Foo`
type SrcLocModule = String

-- | Type of the name of a function in a @CallSite@
-- | e.g. `proveEverything`
type SrcFun = String

-- | Type of a filename of a @SrcLoc@
-- | e.g. `src/full/Agda/Utils/Foo.hs`
type SrcLocFile = String

-- | Type of a line number of a @SrcLoc@
type SrcLocLine = Int

-- | Type of a column of a @SrcLoc@
type SrcLocCol = Int

-- | Type of an entry in  a @CallStack@
type CallSite = (SrcFun, SrcLoc)

-- | Type of a filter for @CallSite@
type CallSiteFilter = CallSite -> Bool

-- * Simple String representations
-- Note that there are @Agda.Syntax.Common.Pretty@ instances defined in @Agda.Utils.CallStack.Pretty@

-- | The same as the un-exported internal function in @GHC.Exceptions (prettyCallStackLines)@
--  Prints like: @doFoo, called at foo.hs:190:24 in main:Main@
prettyCallSite :: CallSite -> String
prettyCallSite (fun, loc) = fun ++ ", called at " ++ prettySrcLoc loc

-- | Pretty-print a @CallStack@. This has a few differences from @GHC.Stack.prettyCallStackLines@.
-- We omit the "CallStack (from GetCallStack)" header line for brevity.
-- If there is only one entry (which is common, due to the manual nature of the @HasCallStack@ constraint),
-- shows the entry on one line. If there are multiple, then the following lines are indented.
prettyCallStack :: CallStack -> String
prettyCallStack cs = case map prettyCallSite (getCallStack cs) of
  []                  -> "(empty CallStack)"
  firstLoc : restLocs -> intercalate "\n" (firstLoc : (map ("  " ++) restLocs))

-- * Generic utilities over CallStack and CallSite

-- | Get the most recent @CallSite@ in a @CallStack@, if there is one.
headCallSite :: CallStack -> Maybe CallSite
headCallSite = listToMaybe . getCallStack

-- | @CallStack@ comprising only the most recent @CallSite@
truncatedCallStack :: CallStack -> CallStack
truncatedCallStack cs = maybe emptyCallStack (fromCallSiteList . pure) (headCallSite cs)

-- | Transform a @CallStack@ by transforming its list of @CallSite@
overCallSites :: ([CallSite] -> [CallSite]) -> CallStack -> CallStack
overCallSites f = fromCallSiteList . f . getCallStack

-- | Transform a @CallStack@ by filtering each @CallSite@
filterCallStack :: CallSiteFilter -> CallStack -> CallStack
filterCallStack = overCallSites . filter

-- | Pops n entries off a @CallStack@ using @popCallStack@.
-- Note that frozen callstacks are unaffected.
popnCallStack :: Word -> CallStack -> CallStack
popnCallStack 0 = id
popnCallStack n = (popnCallStack (n - 1)) . popCallStack

withNBackCallStack :: HasCallStack => Word -> (CallStack -> b) -> b
withNBackCallStack n f = f (popnCallStack n from)
  where
    -- This very line (always dropped):
    here = callStack
    -- The invoker (n = 0):
    from = popCallStack here

withCurrentCallStack :: HasCallStack => (CallStack -> b) -> b
withCurrentCallStack = withNBackCallStack 0
  -- 0 => this line in this utility function.
  -- 1 => the invocation of this utility function.

withCallerCallStack :: HasCallStack => (CallStack -> b) -> b
withCallerCallStack = withNBackCallStack 1
  -- 0 => this line in this utility function.
  -- 1 => our caller.
  -- 2 => their caller.
