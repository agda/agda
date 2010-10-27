module Literal(Literal(..)) where
import Position
import PPrint

data Literal
        = LString String
        | LChar Char
        | LInt Integer
        | LInteger Integer
        | LBool Bool
        | LRational Rational
        | LNative String
        | LImpossible
        | LNoMatch Position
        deriving (Eq, Ord,Show)

instance PPrint Literal where
    pPrint _ _ (LString s)  = text (show s)
    pPrint _ _ (LChar s)    = text (show s)
    pPrint _ _ (LInt s)     = text (show s)
    pPrint _ _ (LInteger s) = text (show s)
    pPrint _ _ (LBool s)    = text (show s)
    pPrint _ _ (LRational s) = text (show s)
    pPrint _ _ (LNative s)  = text (show s)
    pPrint _ _ LImpossible  = text "_impossible"
    pPrint _ _ (LNoMatch p) = text "_noMatch"
