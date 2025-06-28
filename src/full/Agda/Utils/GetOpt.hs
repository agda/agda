-----------------------------------------------------------------------------
-- |
-- Module      :  Agda.Utils.GetOpt
-- Copyright   :  (c) Sven Panne 2002-2005
-- License     :  BSD-style
--
-- This module provides facilities for parsing the command-line options
-- in a standalone program.  It is essentially a Haskell port of the GNU
-- @getopt@ library.
--
-- It is a fork of "System.Console.GetOpt" from the base package of GHC,
-- written by Sven Panne.
--
-- We modify it to remove the "allow prefixes of long options" behavior.
-----------------------------------------------------------------------------

module Agda.Utils.GetOpt (
   -- * GetOpt
   getOpt, getOpt',
   usageInfo,
   ArgOrder(..),
   OptDescr(..),
   ArgDescr(..),
) where

import Prelude
import Data.List (find)

-- | What to do with options following non-options.
data ArgOrder a
  = RequireOrder                -- ^ no option processing after first non-option
  | Permute                     -- ^ freely intersperse options and non-options
  | ReturnInOrder (String -> a) -- ^ wrap non-options into options

{-|
Each 'OptDescr' describes a single option.

The arguments to 'Option' are:

* list of short option characters

* list of long option strings (without \"--\")

* argument descriptor

* explanation of option for user
-}
data OptDescr a =
  Option               -- ^ description of a single options:
    [Char]             -- ^ list of short option characters
    [String]           -- ^ list of long option strings (without "--")
    (ArgDescr a)       -- ^ argument descriptor
    String             -- ^ explanation of option for user

-- | Describes whether an option takes an argument or not, and if so
-- how the argument is injected into a value of type @a@.
data ArgDescr a
  = NoArg                   a          -- ^ no argument expected
  | ReqArg (String       -> a) String  -- ^ option requires argument
  | OptArg (Maybe String -> a) String  -- ^ optional argument

instance Functor ArgOrder where
  fmap _ RequireOrder      = RequireOrder
  fmap _ Permute           = Permute
  fmap f (ReturnInOrder g) = ReturnInOrder (f . g)

instance Functor OptDescr where
  fmap f (Option a b argDescr c) = Option a b (fmap f argDescr) c

instance Functor ArgDescr where
  fmap f (NoArg a)    = NoArg (f a)
  fmap f (ReqArg g s) = ReqArg (f . g) s
  fmap f (OptArg g s) = OptArg (f . g) s

-- | Kind of command line argument (internal use only):
data OptKind a
  = Opt       a        -- ^  an option
  | UnreqOpt  String   -- ^  an un-recognized option
  | NonOpt    String   -- ^  a non-option
  | EndOfOpts          -- ^  end-of-options marker (i.e. "--")
  | OptErr    String   -- ^  something went wrong...

-- | Return a string describing the usage of a command, derived from
-- the header (first argument) and the options described by the
-- second argument.
usageInfo ::
     String            -- ^ header
  -> [OptDescr a]      -- ^ option descriptors
  -> String            -- ^ nicely formatted description of options
usageInfo header optDescr = unlines (header:table)
   where
     (ss, ls, ds)   = unzip3 $ concatMap fmtOpt optDescr
     table          = zipWith3 paste (sameLen ss) (sameLen ls) ds
     paste x y z    = "  " ++ x ++ "  " ++ y ++ "  " ++ z
     sameLen xs     = flushLeft ((maximum . map length) xs) xs
     flushLeft n xs = [ take n (x ++ repeat ' ') | x <- xs ]

fmtOpt :: OptDescr a -> [(String, String, String)]
fmtOpt (Option sos los ad descr) =
   case lines descr of
     []     -> [(sosFmt, losFmt, "")]
     (d:ds) ->  (sosFmt, losFmt, d) : [ ("", "", d') | d' <- ds ]
   where
     sepBy _  []     = ""
     sepBy _  [x]    = x
     sepBy ch (x:xs) = x ++ ch:' ':sepBy ch xs
     sosFmt = sepBy ',' (map (fmtShort ad) sos)
     losFmt = sepBy ',' (map (fmtLong  ad) los)

fmtShort :: ArgDescr a -> Char -> String
fmtShort (NoArg  _   ) so = "-" ++ [so]
fmtShort (ReqArg _ ad) so = "-" ++ [so] ++ " " ++ ad
fmtShort (OptArg _ ad) so = "-" ++ [so] ++ "[" ++ ad ++ "]"

fmtLong :: ArgDescr a -> String -> String
fmtLong (NoArg  _   ) lo = "--" ++ lo
fmtLong (ReqArg _ ad) lo = "--" ++ lo ++ "=" ++ ad
fmtLong (OptArg _ ad) lo = "--" ++ lo ++ "[=" ++ ad ++ "]"

{-|
Process the command-line, and return the list of values that matched
(and those that didn\'t). The arguments are:

* The order requirements (see 'ArgOrder')

* The option descriptions (see 'OptDescr')

* The actual command line arguments (presumably got from
  'GHC.Internal.System.Environment.getArgs').

'getOpt' returns a triple consisting of the option arguments, a list
of non-options, and a list of error messages.
-}
getOpt :: ArgOrder a                   -- ^ non-option handling
       -> [OptDescr a]                 -- ^ option descriptors
       -> [String]                     -- ^ the command-line arguments
       -> ([a], [String], [String])    -- ^ @(options, non-options, error messages)@
getOpt ordering optDescr args = (os, xs, es ++ map errUnrec us)
  where
    (os, xs, us, es) = getOpt' ordering optDescr args

{-|
This is almost the same as 'getOpt', but returns a quadruple
consisting of the option arguments, a list of non-options, a list of
unrecognized options, and a list of error messages.
-}
getOpt' :: ArgOrder a                           -- ^ non-option handling
        -> [OptDescr a]                         -- ^ option descriptors
        -> [String]                             -- ^ the command-line arguments
        -> ([a], [String], [String], [String])  -- ^ @(options, non-options, unrecognized, error messages)@
getOpt' _        _        []         =  ([], [], [], [])
getOpt' ordering optDescr (arg:args) = procNextOpt opt ordering
   where
     procNextOpt (Opt o)      _                 = (o:os, xs, us, es)
     procNextOpt (UnreqOpt u) _                 = (os, xs, u:us, es)
     procNextOpt (NonOpt x)   RequireOrder      = ([], x:rest, [], [])
     procNextOpt (NonOpt x)   Permute           = (os, x:xs, us, es)
     procNextOpt (NonOpt x)   (ReturnInOrder f) = (f x :os, xs, us, es)
     procNextOpt EndOfOpts    RequireOrder      = ([], rest, [], [])
     procNextOpt EndOfOpts    Permute           = ([], rest, [], [])
     procNextOpt EndOfOpts    (ReturnInOrder f) = (map f rest, [], [], [])
     procNextOpt (OptErr e)   _                 = (os, xs, us, e:es)

     (opt, rest) = getNext arg args optDescr
     (os, xs, us, es) = getOpt' ordering optDescr rest

-- | Take a look at the next cmd line arg and decide what to do with it.
getNext :: String -> [String] -> [OptDescr a] -> (OptKind a, [String])
getNext ('-':'-':[]) rest _        = (EndOfOpts, rest)
getNext ('-':'-':xs) rest optDescr = longOpt xs rest optDescr
getNext ('-': x :xs) rest optDescr = shortOpt x xs rest optDescr
getNext a            rest _        = (NonOpt a, rest)

-- | Handle long option.
longOpt :: String -> [String] -> [OptDescr a] -> (OptKind a, [String])
longOpt ls rs optDescr = long ads arg rs
   where
     (opt, arg) = break (== '=') ls
     getWith p = [ o | o@(Option _ xs _ _) <- optDescr
                     , find (p opt) xs /= Nothing ]
     options    = getWith (==)
     -- Diff to System.Console.GetOpt here: do not allow prefixes
     ads       = [ ad | Option _ _ ad _ <- options ]
     optStr    = ("--" ++ opt)

     long (_:_:_)      _        rest     = (errAmbig options optStr, rest)
     long [NoArg  a  ] []       rest     = (Opt a, rest)
     long [NoArg  _  ] ('=':_)  rest     = (errNoArg optStr, rest)
     long [ReqArg _ d] []       []       = (errReq d optStr, [])
     long [ReqArg f _] []       (r:rest) = (Opt (f r), rest)
     long [ReqArg f _] ('=':xs) rest     = (Opt (f xs), rest)
     long [OptArg f _] []       rest     = (Opt (f Nothing), rest)
     long [OptArg f _] ('=':xs) rest     = (Opt (f (Just xs)), rest)
     long _            _        rest     = (UnreqOpt ("--" ++ ls), rest)

-- | Handle short option.
shortOpt :: Char -> String -> [String] -> [OptDescr a] -> (OptKind a, [String])
shortOpt y ys rs optDescr = short ads ys rs
  where
    options = [ o  | o@(Option ss _ _ _) <- optDescr, s <- ss, y == s ]
    ads     = [ ad | Option _ _ ad _ <- options ]
    optStr  = '-':[y]

    short (_:_:_)        _  rest     = (errAmbig options optStr, rest)
    short (NoArg  a  :_) [] rest     = (Opt a, rest)
    short (NoArg  a  :_) xs rest     = (Opt a, ('-':xs):rest)
    short (ReqArg _ d:_) [] []       = (errReq d optStr, [])
    short (ReqArg f _:_) [] (r:rest) = (Opt (f r), rest)
    short (ReqArg f _:_) xs rest     = (Opt (f xs), rest)
    short (OptArg f _:_) [] rest     = (Opt (f Nothing), rest)
    short (OptArg f _:_) xs rest     = (Opt (f (Just xs)), rest)
    short []             [] rest     = (UnreqOpt optStr, rest)
    short []             xs rest     = (UnreqOpt optStr, ('-':xs):rest)

-- * Miscellaneous error formatting

errAmbig :: [OptDescr a] -> String -> OptKind a
errAmbig ods optStr = OptErr (usageInfo header ods)
   where
     header = "option `" ++ optStr ++ "' is ambiguous; could be one of:"

errReq :: String -> String -> OptKind a
errReq d optStr = OptErr ("option `" ++ optStr ++ "' requires an argument " ++ d ++ "\n")

errUnrec :: String -> String
errUnrec optStr = "unrecognized option `" ++ optStr ++ "'\n"

errNoArg :: String -> OptKind a
errNoArg optStr = OptErr ("option `" ++ optStr ++ "' doesn't allow an argument\n")
