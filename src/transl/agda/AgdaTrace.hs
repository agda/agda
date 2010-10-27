-- | Compatibility wrapper for 'trace'.
--   Could import different modules depending on the compiler version
module AgdaTrace(trace) where
import Debug.Trace (trace) {- needs -package lang in GHC -}
