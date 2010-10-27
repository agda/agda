{-| Fast strings

Implementation by ??

Documentation by Andreas Abel: I have the feeling this module has been
messed up.  Originally, a fast string may have been a pair of a unique
identifier plus a hash code.  The actual string contents could be
looked up in a string table using the hash code.  But now a fast
string contains also the literal string, so I do not see why one would
need a hashtable any more.  Also, I do not know why they are called
fast strings.  The only feature that is left is that they carry a
unique identifier.

-}

-- UNFORTUNATELY, THESE SHORT COMMENTS FOR EACH EXPORTED ID ARE NOT SUPPORTED BY HADDOCK

module FString(
  -- * Types
  FString,  -- fast strings
  StrTable, -- hash table to create and resolve strings (state)
  -- * Constructors
  emptyStrTable, -- create a new string table
  hmkFString,    -- create a new fast string
  -- * Selectors
  getFString,    -- resolve a fast string
  getFStrNo,     -- get unique number of fast string
  -- * Temporary fast strings
  tmpFString,    -- create a temporary fast string which is not registered into the string table
  isTmpFString   -- is a fast string temporary ?
) where

import Hash
import Error
import qualified AltIntMap as I
import PPrint
import Util(mkSet)

-- | This was the original documentation which does not hold any more:
--
-- Fast strings may be represented by a number and the real string, or just by
-- a string (not so fast).  The fast strings are made by using a hash table
-- were old strings are kept.
data FString = N !Int !Hash String -- ^ unique number, hash value, actual string

-- | fast string equality by comparing unique numbers
instance Eq FString where
    N n _ _ == N n' _ _ = n == n'
    x       /= y        = not (x==y)

-- | "fast" string ordering by using the actual string
instance Ord FString where
    N _ _ s <= N _ _ s' = s <= s'

instance Show FString where
--    showsType _ = showString "FString"
    showsPrec p (N n _ s) = showsPrec p s

instance Hashable FString where
    hash (N _ h _) = h

instance PPrint FString where
    pPrint _ _ x = text (show x)


hashStr :: String -> Hash
hashStr s = hash (f s 0)
        where f "" r = r
              f (c:cs) r = f cs (r*16+r+fromEnum c)

-- | this function is probably messed up
getFString :: FString -> String
getFString (N n _ s) = s        -- ++":"++show n

getFStrNo :: FString -> Int
getFStrNo (N n _ _) = n

-- | unique identifiers for fast strings start at 100
startNo :: Int
startNo = 100
-- ^ just some start number

-- | A string table is a pair T k ht of an integer k, denoting the next free
-- unique identifier available plus a hashtable ht.
-- A hashtable maps an Int (hash) to a list of fast strings.
data StrTable = T !Int (I.IntMap [FString]) deriving (Show)

emptyStrTable = T startNo I.empty

-- NEED TO QUOTE the @ for Haddock
{-| Making a string fast

hmkFString tbl\@(T k ht) s = (tbl1, fs)

If s is already stored in tbl, then tbl = tbl1,
and fs is the fast string retrieved from tbl.

Otherwise tbl1 = T (k+1) ht' and fs = N k h s,
where ht' is ht extended by a hash for the new string s,
and h is the hashcode generated from s.
-}
hmkFString :: StrTable -> String -> (StrTable, FString)
hmkFString tbl@(T k ht) s =
    let h = hashStr s
        hi = hashToInt maxBound h
    in  case I.ilookup hi ht of
            Just fss -> loc fss
                where loc [] = let fs = N k h s in (T (k+1) (I.add (hi, fs:fss) ht), fs)
                      loc (fs@(N _ _ s'):fss) = if s == s' then (tbl, fs) else loc fss
            Nothing -> let fs = N k h s in (T (k+1) (I.add (hi, [fs]) ht), fs)

-- | all string tables are equal
instance Eq StrTable
        where _ == _  =  True
        -- Just for convenience

-- | Temporary fast strings have an absolute identifying number
-- greater equal to one million.
tmpOffs = 1000000 :: Int

-- | Temporary fast strings are not stored in the string table.
tmpFString :: Int -> String -> FString
tmpFString n s = N (tmpOffs + n) (hashStr s) s

isTmpFString :: FString -> Bool
isTmpFString (N n _ _) = n >= tmpOffs
