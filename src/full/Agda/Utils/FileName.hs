{-# LANGUAGE CPP, DeriveDataTypeable #-}

{-| Operations on file names. -}
module Agda.Utils.FileName
  ( AbsolutePath
  , filePath
  , mkAbsolute
  , absolute
  , (===)
  , splitFilePath
  , splitExt
  , setExtension
  , splitPath
  , unsplitPath
  , dropDirectory
  , addSlash
  , slash
  , slashes
  , nameChar
  , name
  , nonEmptyName
  , path
  , pathOfLength
  , tests
  ) where

import Agda.Utils.TestHelpers
import Agda.Utils.QuickCheck
import Data.Function
import Data.Generics
import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad
import System.Directory
import System.FilePath hiding (splitPath)

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Paths which are known to be absolute.
--
-- Note that the 'Eq' and 'Ord' instances do not check if different
-- paths point to the same files or directories.

newtype AbsolutePath = AbsolutePath { filePath :: FilePath }
  deriving (Show, Eq, Ord, Typeable, Data)

-- | The paths have to be absolute, valid and normalised, without
-- trailing path separators.

absolutePathInvariant :: AbsolutePath -> Bool
absolutePathInvariant (AbsolutePath f) =
  isAbsolute f &&
  isValid f &&
  f == normalise f &&
  f == dropTrailingPathSeparator f

-- | Constructs 'AbsolutePath's.
--
-- Precondition: The path must be absolute.

mkAbsolute :: FilePath -> AbsolutePath
mkAbsolute f
  | isAbsolute f =
      AbsolutePath $ dropTrailingPathSeparator $ normalise f
  | otherwise    = __IMPOSSIBLE__

prop_mkAbsolute f =
  absolutePathInvariant $ mkAbsolute (pathSeparator : f)

-- | Makes the path absolute.
--
-- This function raises an @__IMPOSSIBLE__@ error if
-- 'canonicalizePath' does not return an absolute path.

absolute :: FilePath -> IO AbsolutePath
absolute f = mkAbsolute <$> canonicalizePath f

-- | Tries to establish if the two file paths point to the same file
-- (or directory).

infix 4 ===

(===) :: FilePath -> FilePath -> IO Bool
p1 === p2 = do
  p1 <- canonicalizePath p1
  p2 <- canonicalizePath p2
  return $ equalFilePath p1 p2

splitFilePath :: FilePath -> (FilePath, String, String)
#ifdef mingw32_HOST_OS
splitFilePath (drive:':':s) = let (path, file, ext) = splitFilePath s
                              in (drive:':':path, file, ext)
#endif
splitFilePath s =
    case span (`notElem` slashes) $ reverse s of
	(elif, sl:htap)
	    | sl `elem` slashes -> let (n,e) = splitExt $ reverse elif in
                                    (reverse (slash:htap), n, e)
	(elif, "")	    -> let (n,e) = splitExt $ reverse elif in
				("", n, e)
	_		    -> error $ "impossible: splitFilePath " ++ show s

-- | The extension includes the dot
splitExt :: FilePath -> (String, String)
splitExt x =
    case span (/='.') $ reverse x of
	(txe, '.':elif)	-> (reverse elif, '.' : reverse txe)
	(elif, "")	-> (reverse elif, "")
	_		-> error $ "impossible: splitExt " ++ show x

-- | Change the extension of a filename
setExtension :: String -> FilePath -> FilePath
setExtension ext x = p ++ n ++ ext
    where
	(p,n,_) = splitFilePath x

-- | Breaks up a path (possibly including a file) into a list of
-- drives\/directories (with the file at the end).

splitPath :: FilePath -> [FilePath]
#ifdef mingw32_HOST_OS
splitPath (drive:':':cs) = case splitPath cs of
                             (path:paths) -> (drive:':':path):paths
                             []           -> [[drive,':',slash]]
#endif
splitPath "" = []
splitPath (c : cs) | c `elem` slashes = split cs
                   | otherwise        = split (c : cs)
  where
  split path = case span (`notElem` slashes) path of
    ("", "")        -> []
    (dir, "")       -> [dir]
    (dir, _ : path) -> dir : split path

-- | The moral inverse of splitPath.

unsplitPath :: [FilePath] -> FilePath
#ifdef mingw32_HOST_OS
unsplitPath ((drive:':':path):paths) = drive:':':unsplitPath (path:paths)
#endif
unsplitPath dirs = concat $ intersperse [slash] $ "" : dirs ++ [""]

prop_splitPath_unsplitPath =
  forAll (listOf name) $ \dirs ->
    splitPath (unsplitPath dirs) == dirs

prop_splitPath =
  forAll positive		   $ \n ->
  forAll (vectorOf n nonEmptyName) $ \dirs ->
    let path = concat $ intersperse [slash] dirs
    in
    genericLength (splitPath   path)                    == n
    &&
    genericLength (splitPath $ slash : path)            == n
    &&
    genericLength (splitPath $ path ++ [slash])         == n
    &&
    genericLength (splitPath $ slash : path ++ [slash]) == n

-- | Given a path (not including a file) @'dropDirectory' n@ removes
-- the last @n@ directories in the path (if any).
--
-- Precondition: @n '>=' 0@, and the path has to be absolute.

dropDirectory :: Integral i => i -> FilePath -> FilePath
dropDirectory n =
  unsplitPath . reverse . genericDrop n . reverse . splitPath

-- The complexity of the following property, coupled with the
-- simplicity of dropDirectory, indicates that another representation
-- of paths should be used.

prop_dropDirectory =
  forAll natural	  $ \n ->
  forAll path		  $ \p ->
  forAll (pathOfLength n) $ \dirs ->
  forAll nonEmptyName $ \name ->
    dropDirectory n "" == "/"
    &&
    dropDirectory n [slash] == "/"
    &&
    dropDirectory n (addSlash p) == dropDirectory n p
    &&
    let p' = p ++ name in
    dropDirectory n (p' ++ dirs) =^= p'
  where
  infix 4 =^=
  p1 =^= p2 = surround p1 == surround p2

  surround = addSlash . addInitSlash
  addInitSlash cs@(c : _) | c == slash = cs
  addInitSlash cs                      = slash : cs

#if 0
#ifdef mingw32_HOST_OS
canonify (drive:':':xs) ys =
    case ys of
	drive':':':ys'
	    | drive == drive'	-> canonify' xs ys'
	    | otherwise		-> ys
	_			-> canonify' xs ys
#endif
canonify xs ys = canonify' xs ys

canonify' (x:xs) (y:ys)
    | x == y	    = canonify' xs ys
canonify' [] ys	    = ys
canonify' (s:_) ys
    | s == slash    = ys
canonify' xs ys	    = dotdot xs ++ ys

dotdot []	    = []
dotdot (s:xs)
    | s == slash    = slash : dotdot xs
dotdot xs	    =
    case break (== slash) xs of
	(_, xs)	-> ".." ++ dotdot xs
#endif

addSlash "" = ""
addSlash [c]
    | c `elem` slashes = [slash]
    | otherwise	       = [c,slash]
addSlash (c:s) = c : addSlash s

#ifdef mingw32_HOST_OS
slash   = '\\'
slashes = ['\\','/']
#else
slash = '/'
slashes = ['/']
#endif

------------------------------------------------------------------------
-- Generators

instance Arbitrary AbsolutePath where
  arbitrary = mk . take 3 . map (take 2) <$>
                listOf (listOf1 (elements "a1"))
    where mk ps = AbsolutePath (joinPath $ [pathSeparator] : ps)

-- | Generates a character distinct from 'slash' (it may be @\'.\'@).

nameChar :: Gen Char
nameChar = elements $ filter (not . (`elem` forbidden)) chars
  where
  chars = "." ++ ['a' .. 'g']
  forbidden = [slash]

-- | Generates a possibly empty string of 'nameChar's.

name :: Gen FilePath
name = listOf nameChar

-- | Generates a non-empty string of 'nameChar's.

nonEmptyName :: Gen FilePath
nonEmptyName = listOf1 nameChar

-- | Generates a possibly empty path (without any drive).

path :: Gen FilePath
path = listOfElements chars
  where
  chars = "/." ++ ['a' .. 'g']

-- | @'pathOfLength' n@ generates a path which contains @n '+' 1@
-- 'slash'es and starts and ends with a 'slash'.

pathOfLength :: Int -> Gen FilePath
pathOfLength n = fmap ((++ [slash]) . concat) $
  vectorOf n (fmap (slash :) name)

prop_pathOfLength =
  forAll natural	  $ \n ->
  forAll (pathOfLength n) $ \path ->
    dropDirectory n path == [slash]
    &&
    genericLength (filter (== slash) path) == n + 1

------------------------------------------------------------------------
-- All tests

tests = runTests "Agda.Utils.FileName"
  [ quickCheck' absolutePathInvariant
  , quickCheck' prop_mkAbsolute
  , quickCheck' prop_splitPath_unsplitPath
  , quickCheck' prop_splitPath
  , quickCheck' prop_dropDirectory
  , quickCheck' prop_pathOfLength
  ]
