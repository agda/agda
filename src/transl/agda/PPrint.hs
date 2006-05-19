-- | PPrint class (built on top of AgdaPretty)
module PPrint(PPrint(..), module AgdaPretty, PDetail(..),
        ppReadable,ppAll, ppDebug, ppString,
        pparen, sepList,nsepList,csepList,ppr,pppr,pIText) where
import AgdaPretty

data PDetail = PDReadable | PDAll | PDDebug deriving (Eq, Ord)



class PPrint a where
    pPrint :: PDetail -> Int -> a -> IText
--    pPrint _ _ x = text ("***"++show x++"***")

ppReadable :: (PPrint a) => a -> String
ppReadable = ppr PDReadable



ppAll :: (PPrint a) => a -> String
ppAll = ppr PDAll

ppDebug :: (PPrint a) => a -> String
ppDebug = ppr PDDebug

lineWidth = 80::Int
linePref = 70::Int

ppString :: (PPrint a) => a -> String
ppString = init . ppReadable

ppr d = pretty lineWidth linePref . pPrint d 0

pppr d p = pretty lineWidth linePref . pPrint d p

pIText t = pretty lineWidth linePref t

instance PPrint Int where
    pPrint _ _ x = text (show x)

instance PPrint Integer where
    pPrint _ _ x = text (show x)

instance PPrint Bool where
    pPrint _ _ x = text (show x)

instance PPrint Char where
    pPrint _ _ x = text (show x)

instance (PPrint a, PPrint b) => PPrint (a, b) where
    pPrint d _ (x, y) = text "(" ~. nseparate [pPrint d 0 x ~. text ", ", pPrint d 0 y] ~. text ")"

instance (PPrint a, PPrint b, PPrint c) => PPrint (a, b, c) where
    pPrint d _ (x, y, z) = text "(" ~. nseparate [pPrint d 0 x ~. text ", ", pPrint d 0 y ~. text ", ", pPrint d 0 z] ~. text ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d) => PPrint (a, b, c, d) where
    pPrint d _ (x, y, z, w) = text "(" ~. nseparate [pPrint d 0 x ~. text ", ", pPrint d 0 y ~. text ", ", pPrint d 0 z ~. text ", ", pPrint d 0 w] ~. text ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d, PPrint e)
         => PPrint (a, b, c, d, e) where
    pPrint d _ (x, y, z, w, u) = text "(" ~. nseparate [pPrint d 0 x ~. text ", ", pPrint d 0 y ~. text ", ", pPrint d 0 z ~. text ", ", pPrint d 0 w ~. text ", ", pPrint d 0 u] ~. text ")"



instance (PPrint a) => PPrint [a] where
    pPrint d _ [] = text "[]"
    pPrint d _ xs = let (y:ys) = reverse (map (pPrint d 0) xs)
                        f =  \s -> (~.) s (text ",")
                        ys' = map f ys
                        xs' = reverse (y:ys')
                    in  text "[" ~. cseparate xs' ~. text "]"
--                  in  text "[" ~. separate xs' ~. text "]"


instance (PPrint a, PPrint b) => PPrint (Either a b) where
    pPrint d p (Left x) = pparen (p>9) (text"(Left " ~. pPrint d 10 x ~. text")")
    pPrint d p (Right x) = pparen (p>9) (text"(Right " ~. pPrint d 10 x ~. text")")

instance (PPrint a) => PPrint (Maybe a) where
    pPrint _ _ Nothing = text"Nothing"
    pPrint d p (Just x) = pparen (p>9) (text"Just (" ~. pPrint d 10 x ~. text")")

instance PPrint () where
    pPrint _ _ _ = text "()"

pparen False x = x
pparen True  x = text"(" ~. x ~. text")"

sepList [] _ = text ""
sepList xs s = separate (map (\x->x ~. s) (init xs) ++ [last xs])

nsepList [] _ = text ""
nsepList xs s = nseparate  (map (\x->x ~. s) (init xs) ++ [last xs])


csepList [] _ = text ""
csepList xs s = cseparate  (map (\x->x ~. s) (init xs) ++ [last xs])
