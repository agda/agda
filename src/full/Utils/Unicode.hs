
module Utils.Unicode
    ( UTF8
    , readFileUTF8
    , writeFileUTF8
    , toUTF8
    , fromUTF8
    , isUnicodeId
    , isUnicodeOp
    ) where

import Data.Bits
import Data.List

import Utils.Monad

-- Unicode ----------------------------------------------------------------

-- Characters
uPlusMinusSign				= '\xb1'
uMultiplicationSign			= '\xd7'
uDivisionSign				= '\xf7'
uPrime  				= '\x2032'
uDoublePrime  				= '\x2033'
uTriplePrime  				= '\x2034'
uQuadruplePrime				= '\x2057'
uElementOf				= '\x2208'
uNotAnElementOf				= '\x2209'
uSmallElementOf				= '\x220a'
uContainsAsMember			= '\x220b'
uDoesNotContainAsMember			= '\x220c'
uSmallContainsAsMember			= '\x220d'
uMinusOrPlusSign			= '\x2213'
uDotPlus				= '\x2214'
uDivisionSlash				= '\x2215'
uSetMinus				= '\x2216'
uAsteriskOperator			= '\x2217'
uRingOperator				= '\x2218'
uBulletOperator				= '\x2219'
uProportionalTo				= '\x221d'
uDivides				= '\x2223'
uDoesNotDivide				= '\x2224'
uParallelTo				= '\x2225'
uNotParallelTo				= '\x2226'
uLogicalAnd				= '\x2227'
uLogicalOr				= '\x2228'
uIntersection				= '\x2229'
uUnion					= '\x222a'
uDotMinus				= '\x2238'
uTildeOperator				= '\x223c'
uAsymptoticallyEqualTo			= '\x2243'
uNotAsymptoticallyEqualTo		= '\x2244'
uApproximatelyEqualTo			= '\x2245'
uNotApproximatelyButNotActuallyEqualTo	= '\x2246'
uNeitherApproximatelyNorActuallyEqualTo = '\x2247'
uAlmostEqualTo				= '\x2248'
uNotAlmostEqualTo			= '\x2249'
uAlmostEqualOrEqualTo			= '\x224a'
uTripleTilde				= '\x224b'
uApprochesTheLimit			= '\x2250'
uColonEquals				= '\x2254'
uDeltaEqualTo				= '\x225c'
uEqualToByDefinition			= '\x225d'
uMeasuredBy				= '\x225e'
uQuestionedEqualTo			= '\x225f'
uNotEqualTo				= '\x2260'
uIdenticalTo				= '\x2261'
uNotIdenticalTo				= '\x2262'
uStrictlyEquivalentTo			= '\x2263'
uLessThanOrEqualTo			= '\x2264'
uGreaterThanOrEqualTo			= '\x2265'
uLessThanOverEqualTo			= '\x2266'
uGreaterThanOverEqualTo			= '\x2267'
uMuchLessThan				= '\x226a'
uMuchGreaterThan			= '\x226b'
uSubsetOf				= '\x2282'
uSuperSetOf				= '\x2283'
uNotASubsetOf				= '\x2284'
uNotASupersetOf				= '\x2285'
uSubsetOfOrEqualTo			= '\x2286'
uSupersetOfOrEqualTo			= '\x2287'
uNeitherASubsetOfNorEqualTo		= '\x2288'
uNeitherASupersetOfNorEqualTo		= '\x2289'
uSquareImageOf				= '\x228f'
uSquareOriginalOf			= '\x2290'
uSquareImageOfOrEqualTo			= '\x2291'
uSquareOriginalOfOrEqualTo		= '\x2292'
uSquareCap				= '\x2293'
uSquareCup				= '\x2294'
uCircledPlus				= '\x2295'
uCircledMinus				= '\x2296'
uCircledTimes				= '\x2297'
uCircledDivisionSlash			= '\x2298'
uCircledDotOperator			= '\x2299'
uCircledRingOperator			= '\x229a'
uCircledAsteriskOperator		= '\x229b'
uCircledEquals				= '\x229c'
uCircledDash				= '\x229d'
uRightTack				= '\x22a2'
uLeftTack				= '\x22a3'
uAssertion				= '\x22a6'
uModels					= '\x22a7'
uTrue					= '\x22a8'
uForces					= '\x22a9'
uArrows	= ['\x2190'..'\x21ff']
uGeometricShapes = ['\x25a0' .. '\x25ff']

uNotSign		= '\xac'
uForAll			= '\x2200'
uComplement		= '\x2201'
uPartialDifferential	= '\x2202'
uThereExists		= '\x2203'
uThereDoesNotExist	= '\x2204'
uEmptySet		= '\x2205'
uIncrement		= '\x2206'
uNabla			= '\x2207'
uEndOfProof		= '\x220e'
uNaryProduct		= '\x220f'
uNaryCoproduct		= '\x2210'
uNarySummations		= '\x2211'
uSquareRoot		= '\x221a'
uCubeRoot		= '\x221b'
uFourthRoot		= '\x221c'
uInfinity		= '\x221e'
uRightAngle		= '\x221f'
uAngle			= '\x2220'
uMeasuredAngle		= '\x2221'
uSphericalAngle		= '\x2222'
uIntegral		= '\x222b'
uDoubleIntegral		= '\x222c'
uTripleIntegral		= '\x222d'
uContourIntegral	= '\x222e'
uDownTack		= '\x22a4'
uUpTack			= '\x22a5'
uNaryLogicalAnd		= '\x22c0'
uNaryLogicalOr		= '\x22c1'
uNaryIntersection	= '\x22c2'
uNaryUnion		= '\x22c3'
uGreekCapitalLetters	= ['\x391'..'\x3a1']
			++['\x3a3'..'\x3a9']
uGreekSmallLetters	= ['\x3b1'..'\x3c9']
uBlackStar		= '\x2605'
uWhiteStar		= '\x2606'
uSubscriptNumbers       = ['\x2080' .. '\x2089'] -- ₀₁₂₃₄₅₆₇₈₉
uSuperscriptNumbers     = ['\x2070', '\xb9', '\xb2', '\xb3']
                          ++ ['\x2074' .. '\x2079']
                          -- ⁰¹²³⁴⁵⁶⁷⁸⁹
uOtherSubscripts        = ['\x208a' .. '\x208e'] -- ₊₋₌₍₎
uOtherSuperscripts      = ['\x207a' .. '\x207f'] -- ⁺⁻⁼⁽⁾ⁿ
uLetterlikeSymbols      = ['\x2100' .. '\x214c']

-- | Check if a character is a unicode operator symbol.
isUnicodeOp :: Char -> Bool
isUnicodeOp x =
    elem x $
    [ uPlusMinusSign
    , uMultiplicationSign
    , uDivisionSign
    , uPrime
    , uDoublePrime
    , uTriplePrime
    , uQuadruplePrime
    , uElementOf
    , uNotAnElementOf
    , uSmallElementOf
    , uContainsAsMember
    , uDoesNotContainAsMember
    , uSmallContainsAsMember
    , uMinusOrPlusSign
    , uDotPlus
    , uDivisionSlash
    , uSetMinus
    , uAsteriskOperator
    , uRingOperator
    , uBulletOperator
    , uProportionalTo
    , uDivides
    , uDoesNotDivide
    , uParallelTo
    , uNotParallelTo
    , uLogicalAnd
    , uLogicalOr
    , uIntersection
    , uUnion
    , uDotMinus
    , uTildeOperator
    , uAsymptoticallyEqualTo
    , uNotAsymptoticallyEqualTo
    , uApproximatelyEqualTo
    , uNotApproximatelyButNotActuallyEqualTo
    , uNeitherApproximatelyNorActuallyEqualTo
    , uAlmostEqualTo
    , uNotAlmostEqualTo
    , uAlmostEqualOrEqualTo
    , uTripleTilde
    , uApprochesTheLimit
    , uColonEquals
    , uDeltaEqualTo
    , uEqualToByDefinition
    , uMeasuredBy
    , uQuestionedEqualTo
    , uNotEqualTo
    , uIdenticalTo
    , uNotIdenticalTo
    , uStrictlyEquivalentTo
    , uLessThanOrEqualTo
    , uGreaterThanOrEqualTo
    , uLessThanOverEqualTo
    , uGreaterThanOverEqualTo
    , uMuchLessThan
    , uMuchGreaterThan
    , uSubsetOf
    , uSuperSetOf
    , uNotASubsetOf
    , uNotASupersetOf
    , uSubsetOfOrEqualTo
    , uSupersetOfOrEqualTo
    , uNeitherASubsetOfNorEqualTo
    , uNeitherASupersetOfNorEqualTo
    , uSquareImageOf
    , uSquareOriginalOf
    , uSquareImageOfOrEqualTo
    , uSquareOriginalOfOrEqualTo
    , uSquareCap
    , uSquareCup
    , uCircledPlus
    , uCircledMinus
    , uCircledTimes
    , uCircledDivisionSlash
    , uCircledDotOperator
    , uCircledRingOperator
    , uCircledAsteriskOperator
    , uCircledEquals
    , uCircledDash
    , uRightTack
    , uLeftTack
    , uAssertion
    , uModels
    , uTrue
    , uForces
    ] ++ uArrows
      ++ uGeometricShapes

-- | Check if a character is a unicode identifier symbol.
isUnicodeId :: Char -> Bool
isUnicodeId x =
    elem x $
    [ uNotSign
    , uForAll
    , uComplement
    , uPartialDifferential
    , uThereExists
    , uThereDoesNotExist
    , uEmptySet
    , uIncrement
    , uNabla
    , uEndOfProof
    , uNaryProduct
    , uNaryCoproduct
    , uNarySummations
    , uSquareRoot
    , uCubeRoot
    , uFourthRoot
    , uInfinity
    , uRightAngle
    , uAngle
    , uMeasuredAngle
    , uSphericalAngle
    , uIntegral
    , uDoubleIntegral
    , uTripleIntegral
    , uContourIntegral
    , uDownTack
    , uUpTack
    , uNaryLogicalAnd
    , uNaryLogicalOr
    , uNaryIntersection
    , uNaryUnion
    , uBlackStar
    , uWhiteStar
    ] ++ uGreekSmallLetters
      ++ uGreekCapitalLetters
      ++ uSubscriptNumbers
      ++ uSuperscriptNumbers
      ++ uOtherSubscripts
      ++ uOtherSuperscripts
      ++ uLetterlikeSymbols

-- UTF-8 ------------------------------------------------------------------

type UTF8 = String

readFileUTF8 :: FilePath -> IO String
readFileUTF8 file = fromUTF8 <$> readFile file

writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 file s = writeFile file $ toUTF8 s

toUTF8 :: String -> UTF8
toUTF8 = concatMap utf8
    where
	utf8 c
	    | n <= 0x7F	    = [c]
	    | n <= 0x7FF    = [ mk0 2 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0xFFFF   = [ mk0 3 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0x1FFFFF = [ mk0 4 $ shiftR n 18
			      , mk1 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0x3FFFFFF= [ mk0 3 $ shiftR n 24
			      , mk1 $ shiftR n 18
			      , mk1 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0x7FFFFFF= [ mk0 2 $ shiftR n 30
			      , mk1 $ shiftR n 24
			      , mk1 $ shiftR n 18
			      , mk1 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | otherwise	    = error $ "toUTF8: invalid unicode character " ++ show c
	    where
		n	= fromEnum c
		--bits i    = reverse $ take i $ map (testBit n) [0..7]
		byte0 i	= foldl setBit 0 $ take i [7,6..0]
		byte1	= byte0 1
		mk0 i n	= toEnum $ byte0 i .|. n .&. mask (8 - i)
		mk1 n	= toEnum $ byte1 .|. n .&. mask 6

mask i	= foldl setBit 0 $ take i [0..]

fromUTF8 :: UTF8 -> String
fromUTF8 = map decode . chop
    where
	chop []	     = []
	chop s@(c:_) = w : chop s'
	    where
		(w,s') = splitAt len s
		n = fromEnum c
		len = case findIndex (not . testBit n) [7,6..0] of
			Just 0	-> 1
			Just 2	-> 2
			Just 3	-> 3
			Just 4	-> 4
-- 			Just 5	-> 5
-- 			Just 6	-> 6
			_	-> error $ "fromUTF8: Bad utf-8 character: " ++ show c
	decode [c]  = c
	decode cs   = toEnum buildAll
	    where
		build i k n = shiftL (mask i .&. n) k

		buildAll = foldr (.|.) (build i k n0) $
			   zipWith (build 6) [k-6,k-12..] ns
		    where
			i	= 7 - len
			len	= length cs
			k	= 6 * (len - 1)
			n0 : ns = map fromEnum cs


{-
showBits :: Char -> String
showBits c = unwords $ dropWhile (all (=='0')) $ chop 8 $ map f [31,30..0]
    where
	n = fromEnum c
	f i | testBit n i   = '1'
	    | otherwise	    = '0'
-}
