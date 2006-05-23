{-# OPTIONS -cpp #-}

{-| Operations on file names. -}
module Utils.FileName where

splitFilePath :: FilePath -> (FilePath, String, String)
splitFilePath s =
    case span (/=slash) $ reverse s of
	(elif, sl:htap)
	    | sl == slash   -> let (n,e) = splitExt $ reverse elif in
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

#ifdef mingw32_HOST_OS
canonify (drive:':':xs) ys =
    case ys of
	drive':':':ys'
	    | drive == drive'	-> canonify' xs ys'
	    | otherwise		-> ys
	_			-> canonify' xs ys
#else
canonify = canonify'
#endif
    where
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

addSlash "" = ""
addSlash [c]
    | c == slash    = [slash]
    | otherwise	    = [c,slash]
addSlash (c:s) = c : addSlash s

#ifdef mingw32_HOST_OS
slash = '\\'
#else
slash = '/'
#endif

