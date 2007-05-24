{-# OPTIONS -cpp #-}

{-| Operations on file names. -}
module Utils.FileName where

import Utils.TestHelpers
import Test.QuickCheck
import Data.List
import Control.Monad

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
-- drives/directories (with the file at the end).

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
  forAll (list name) $ \dirs ->
    splitPath (unsplitPath dirs) == dirs

prop_splitPath =
  forAll (positive :: Gen Integer) $ \n ->
  forAll (listOfLength n nonEmptyName) $ \dirs ->
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
-- Precondition: @n '>=' 0@.

dropDirectory :: Integral i => i -> FilePath -> FilePath
dropDirectory n =
  unsplitPath . reverse . genericDrop n . reverse . splitPath

-- The complexity of the following property, coupled with the
-- simplicity of dropDirectory, indicates that another representation
-- of paths should be used.

prop_dropDirectory =
  forAll (natural :: Gen Integer) $ \n ->
  forAll path $ \p ->
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

-- | Generates a character distinct from 'slash' (it may be @\'.\'@).

nameChar :: Gen Char
nameChar = elements $ filter (not . (`elem` forbidden)) chars
  where
  chars = "." ++ ['a' .. 'g']
  forbidden = [slash]

-- | Generates a possibly empty string of 'nameChar's.

name :: Gen FilePath
name = list nameChar

-- | Generates a non-empty string of 'nameChar's.

nonEmptyName :: Gen FilePath
nonEmptyName = nonEmptyList nameChar

-- | Generates a possibly empty path (without any drive).

path :: Gen FilePath
path = list $ elements chars
  where
  chars = "/." ++ ['a' .. 'g']

-- | @'pathOfLength' n@ generates a path which contains @n '+' 1@
-- 'slash'es and starts and ends with a 'slash'.

pathOfLength :: Integral i => i -> Gen FilePath
pathOfLength n = fmap ((++ [slash]) . concat) $
  listOfLength n (fmap (slash :) name)

prop_pathOfLength =
  forAll (natural :: Gen Integer) $ \n ->
  forAll (pathOfLength n) $ \path ->
    dropDirectory n path == [slash]
    &&
    genericLength (filter (== slash) path) == n + 1

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_splitPath_unsplitPath
  quickCheck prop_splitPath
  quickCheck prop_dropDirectory
  quickCheck prop_pathOfLength
