-- | Generic Parser
--
-- Provides generic parsing combinators.
-- Nothing Agda specific.

module Parse(Parser, (+.+), (..+), (+..), (|||), (>>-), (>>>), (||!), (|!!), (.>),
             into, lit, litp, many, many1, succeed, failure, sepBy, count, sepBy1, testp, token, recover,
             ParseResult, parse, sParse, simpleParse) where

import AgdaTrace
import Data.List(nub)

-- @@ Parsing combinatores with good error reporting.

infixr 8 +.+ , ..+ , +..
infix  6 >>- , >>>, `into` , .>
infixr 4 ||| , ||! , |!!

type PErrMsg = String

data FailAt a
        = FailAt !Int [PErrMsg] a                               -- token pos, list of acceptable tokens, rest of tokens
        deriving (Show)
data ParseResult a b
        = Many [(b, Int, a)] (FailAt a)                         -- parse succeeded with many (>1) parses)
        | One b !Int a !(FailAt a)                              -- parse succeeded with one parse
        | None !Bool !(FailAt a)                                -- parse failed. The Bool indicates hard fail
        deriving (Show)

type Parser a b = a -> Int -> ParseResult a b

noFail = FailAt (-1) [] (error "noFail")                -- indicates no failure yet

updFail f (None w f')     = None w (bestFailAt f f')
updFail f (One c n as f') = One c n as (bestFailAt f f')
updFail f (Many cas f')   = let r = bestFailAt f f' in seq r (Many cas r)

bestFailAt f@(FailAt i a t) f'@(FailAt j a' _) =
        if i > j then
            f
        else if j > i then
            f'
        else if i == -1 then
            noFail
        else
            FailAt i (a ++ a') t

-- Alternative
(|||) :: Parser a b -> Parser a b -> Parser a b
p ||| q = \as n ->
    case (p as n, q as n) of
        (pr@(None True  _), _                ) -> pr
        (pr@(None _     f), qr               ) -> updFail f qr
        (    One b k as f , qr               ) -> Many ((b,k,as) : l') (bestFailAt f f') where (l',f') = lf qr
        (    Many  l f    , qr               ) -> Many (        l++l') (bestFailAt f f') where (l',f') = lf qr
    where lf (Many l f)     = (l,          f)
          lf (One b k as f) = ([(b,k,as)], f)
          lf (None _   f)   = ([],         f)

-- Alternative, but with committed choice
(||!) :: Parser a b -> Parser a b -> Parser a b
p ||! q = \as n ->
    case (p as n, q as n) of
        (pr@(None True  _), _                ) -> pr
        (    None _     f , qr               ) -> updFail f qr
        (pr               , _                ) -> pr

processAlts f [] [] = seq f (None False f)
processAlts f [(b,k,as)]  [] = seq f (One b k as f)
processAlts f rs [] = seq f (Many rs f)
processAlts f rs (w@(None True _):_) = seq f w
processAlts f rs (None False f':rws) = processAlts (bestFailAt f f') rs rws
processAlts f rs (One b k as f':rws) = processAlts (bestFailAt f f') (rs++[(b,k,as)]) rws
processAlts f rs (Many rs' f'  :rws) = processAlts (bestFailAt f f') (rs++rs') rws

doMany g cas f = Many [ (g c, n, as) | (c,n,as) <- cas] f

-- Sequence
(+.+) :: Parser a b -> Parser a c -> Parser a (b,c)
p +.+ q =
    \as n->
    case p as n of
        None w f -> None w f
        One b n' as' f ->
            case q as' n' of
                None w f'         -> None w (bestFailAt f f')
                One c n'' as'' f' -> One (b,c) n'' as'' (bestFailAt f f')
                Many cas f'       -> doMany (\x->(b,x)) cas (bestFailAt f f')
        Many bas f ->
            let rss = [ case q as' n' of { None w f -> None w f;
                                           One c n'' as'' f' -> One (b,c) n'' as'' f';
                                           Many cas f' -> doMany (\x->(b,x)) cas f'  }
                        | (b,n',as') <- bas ]
            in  processAlts f [] rss

-- Sequence, throw away first part
(..+) :: Parser a b -> Parser a c -> Parser a c
p ..+ q = -- p +.+ q >>- snd
    \as n->
    case p as n of
        None w f       -> None w f
        One _ n' as' f -> updFail f (q as' n')
        Many bas f     -> processAlts f [] [ q as' n' | (_,n',as') <- bas ]

-- Sequence, throw away second part
(+..) :: Parser a b -> Parser a c -> Parser a b
p +.. q = -- p +.+ q >>- fst
    \as n->
    case p as n of
        None w f -> None w f
        One b n' as' f ->
            case q as' n' of
                None w f'         -> None w (bestFailAt f f')
                One _ n'' as'' f' -> One b n'' as'' (bestFailAt f f')
                Many cas f'       -> doMany (const b) cas (bestFailAt f f')
        Many bas f ->
            let rss = [ case q as' n' of { None w f -> None w f;
                                           One _ n'' as'' f' -> One b n'' as'' f';
                                           Many cas f' -> doMany (const b) cas f' }
                        | (b,n',as') <- bas ]
            in  processAlts f [] rss

-- Return a fixed value
(.>) :: Parser a b -> c -> Parser a c
p .> v =
    \as n->
    case p as n of
      None w f        -> None w f
      One _ n' as' f' -> One v n' as' f'
      Many bas f      -> doMany (const v) bas f

-- Action
(>>-) :: Parser a b -> (b->c) -> Parser a c
p >>- f = \as n->
    case p as n of
        None w f       -> None w f
        One b n as' ff -> One (f b) n as' ff
        Many bas ff    -> doMany f bas ff

-- Action on two items
(>>>) :: Parser a (b,c) -> (b->c->d) -> Parser a d
p >>> f = \as n->
    case p as n of
        None w ff          -> None w ff
        One (b,c) n as' ff -> One (f b c) n as' ff
        Many bas ff        -> doMany (\ (x,y)->f x y) bas ff

-- Use value
into :: Parser a b -> (b -> Parser a c) -> Parser a c
p `into` fq = \as n ->
    case p as n of
        None w f       -> None w f
        One b n' as' f -> updFail f (fq b as' n')
        Many bas f     -> processAlts f [] [ fq b as' n' | (b,n',as') <- bas ]

-- Succeeds with a value
succeed :: b -> Parser a b
succeed v = \as n -> One v n as noFail

-- Always fails.
failure :: PErrMsg -> Parser a b
failure s = \as n -> None False (FailAt n [s] as)

-- Fail completely if parsing proceeds a bit and then fails
mustAll :: Parser a b -> Parser a b
mustAll p = \as n->
        case p as n of
        None False f@(FailAt x _ _) | x/=n -> None True f
        r -> r

-- If first alternative gives partial parse it's a failure
p |!! q = mustAll p ||! q

-- Kleene star
many :: Parser a b -> Parser a [b]
many p = p `into` (\v-> many p >>- (v:))
     ||! succeed []

many1 :: Parser a b -> Parser a [b]
many1 p = p `into` (\v-> many p >>- (v:))

-- Parse an exact number of items
count :: Parser a b -> Int -> Parser a [b]
count p 0 = succeed []
count p k = p +.+ count p (k-1) >>> (:)

-- Non-empty sequence of items separated by something
sepBy1 :: Parser a b -> Parser a c -> Parser a [b]
p `sepBy1` q = p `into` (\v-> many (q ..+ p) >>- (v:))

-- Sequence of items separated by something
sepBy :: Parser a b -> Parser a c -> Parser a [b]
p `sepBy` q = p `sepBy1` q
          ||! succeed []

-- Recognize a literal token
lit :: (Eq a, Show a) => a -> Parser [a] a
lit x = \as n ->
        case as of
        a:as' | a==x -> One a (n+1) as' noFail
        _ -> None False (FailAt n [show x] as)

-- Recognize a token with a predicate
litp :: PErrMsg -> (a->Bool) -> Parser [a] a
litp s p = \as n->
        case as of
        a:as' | p a -> One a (n+1) as' noFail
        _ -> None False (FailAt n [s] as)

-- Generic token recognizer
token :: (a -> Either PErrMsg (b,a)) -> Parser a b
token f = \as n->
        case f as of
            Left s -> None False (FailAt n [s] as)
            Right (b, as') -> One b (n+1) as' noFail

-- Test a semantic value
testp :: String -> (b->Bool) -> Parser a b -> Parser a b
testp s tst p = \ as n ->
    case p as n of
      None w f -> None w f
      o@(One b _ _ _) -> if tst b then o else None False (FailAt n [s] as)
      Many bas f ->
        case [ r | r@(b, _, _) <- bas, tst b] of
            [] -> None False (FailAt n [s] as)
            [(x,y,z)] -> One x y z f
            rs -> Many rs f

-- Try error recovery.
recover :: Parser a b -> ([PErrMsg] -> a -> Maybe (a, b)) -> Parser a b
recover p f = \ as n ->
        case p as n of
            r@(None _ fa@(FailAt n ss ts)) ->
                case f ss ts of
                    Nothing -> r
                    Just (a, b) -> One b (n+1) a fa
            r -> r

-- Parse, and check if it was ok.
parse :: Parser a b -> a -> Either ([PErrMsg],a) [(b, a)]
parse p as =
        case p as 0 of
            None w (FailAt _ ss ts) -> Left (ss,ts)
            One b _ ts _            -> Right [(b,ts)]
            Many bas _              -> Right [(b,ts) | (b,_,ts) <- bas ]

--sParse :: (Show a) => Parser [a] b -> [a] -> Either String b
sParse p as =
        case parse p as of
            Left (ss,ts)     -> Left ("Parse failed at "++pshow ts++", expected one of "++unwords(nub ss)++"\n")
                                  where pshow [] = "<EOF>"
                                        pshow (t:_) = show t
            Right ((b,[]):_)  -> Right b
            Right ((_,t:_):_) -> Left ("Parse failed at "++show t++", expected <EOF>\n")

simpleParse :: (Show a) => Parser [a] b -> [a] -> b
simpleParse p as =
        case sParse p as of
        Left msg -> error msg
        Right x -> x
