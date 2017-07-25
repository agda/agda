
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Compiler.Treeless.Pretty () where

import Control.Arrow ((&&&), (***), first, second)
import Control.Applicative
import Control.Monad.Reader
import Data.Maybe

import Agda.Syntax.Treeless
import Agda.Utils.Pretty

data PEnv = PEnv { pPrec :: Int
                 , pFresh :: [String]
                 , pBound :: [String] }

type P = Reader PEnv

withName :: (String -> P a) -> P a
withName k = withNames 1 $ \[x] -> k x

withNames :: Int -> ([String] -> P a) -> P a
withNames n k = do
  (xs, ys) <- asks $ splitAt n . pFresh
  local (\ e -> e { pFresh = ys }) (k xs)

bindName :: String -> P a -> P a
bindName x = local $ \ e -> e { pBound = x : pBound e }

bindNames :: [String] -> P a -> P a
bindNames xs p = foldr bindName p xs

paren :: Int -> P Doc -> P Doc
paren p doc = do
  n <- asks pPrec
  (if p < n then parens else id) <$> doc

prec :: Int -> P a -> P a
prec p = local $ \ e -> e { pPrec = p }

name :: Int -> P String
name x = asks $ (!! x) . (++ map (("^" ++) . show) [1..]) . pBound

runP :: P a -> a
runP p = runReader p PEnv{ pPrec = 0, pFresh = names, pBound = [] }
  where
    names = [ x ++ i | i <- "" : map show [1..], x <- map (:[]) ['a'..'z'] ]

instance Pretty TTerm where
  prettyPrec p t = runP $ prec p (pTerm t)

opName :: TPrim -> String
opName PAdd = "+"
opName PSub = "-"
opName PMul = "*"
opName PQuot = "quot"
opName PRem = "rem"
opName PGeq = ">="
opName PLt  = "<"
opName PEqI = "==I"
opName PEqF = "==F"
opName PEqS = "==S"
opName PEqC = "==C"
opName PEqQ = "==Q"
opName PIf  = "if_then_else_"
opName PSeq = "seq"

isInfix :: TPrim -> Maybe (Int, Int, Int)
isInfix op =
  case op of
    PMul -> l 7
    PAdd -> l 6
    PSub -> l 6
    PGeq -> non 4
    PLt  -> non 4
    p | isPrimEq p -> non 4
    _    -> Nothing
  where
    l n   = Just (n, n, n + 1)
    r n   = Just (n, n + 1, n)
    non n = Just (n, n + 1, n + 1)

pTerm' :: Int -> TTerm -> P Doc
pTerm' p = prec p . pTerm

pTerm :: TTerm -> P Doc
pTerm t = case t of
  TVar x -> text <$> name x
  TApp (TPrim op) [a, b] | Just (c, l, r) <- isInfix op ->
    paren c $ sep <$> sequence [ pTerm' l a
                               , pure $ text $ opName op
                               , pTerm' r b ]
  TApp (TPrim PIf) [a, b, c] ->
    paren 0 $ (\ a b c -> sep [ text "if" <+> a
                              , nest 2 $ text "then" <+> b
                              , nest 2 $ text "else" <+> c ])
              <$> pTerm' 0 a
              <*> pTerm' 0 b
              <*> pTerm c
  TDef f -> pure $ pretty f
  TCon c -> pure $ pretty c
  TLit l -> pure $ pretty l
  TPrim op | isJust (isInfix op) -> pure $ text ("_" ++ opName op ++ "_")
           | otherwise -> pure $ text (opName op)
  TApp f es ->
    paren 9 $ (\a bs -> sep [a, nest 2 $ fsep bs])
              <$> pTerm' 9 f
              <*> mapM (pTerm' 10) es
  TLam _ -> paren 0 $ withNames n $ \xs -> bindNames xs $
    (\b -> sep [ text ("λ " ++ unwords xs ++ " →")
               , nest 2 b ]) <$> pTerm' 0 b
    where
      (n, b) = lamV t
      lamV (TLam b) = first succ $ lamV b
      lamV t        = (0, t)
  TLet{} -> paren 0 $ withNames (length es) $ \ xs ->
    (\ (binds, b) -> sep [ text "let" <+> vcat [ sep [ text x <+> text "="
                                                     , nest 2 e ] | (x, e) <- binds ]
                              <+> text "in", b ])
      <$> pLets (zip xs es) b
    where
      (es, b) = letV t
      letV (TLet e b) = first (e :) $ letV b
      letV t          = ([], t)

      pLets [] b = ([],) <$> pTerm' 0 b
      pLets ((x, e) : bs) b = do
        e <- pTerm' 0 e
        first ((x, e) :) <$> bindName x (pLets bs b)

  TCase x _ def alts -> paren 0 $
    (\ sc alts defd ->
      sep [ text "case" <+> sc <+> text "of"
          , nest 2 $ vcat (alts ++ [ text "_ →" <+> defd | null alts || def /= TError TUnreachable ]) ]
    ) <$> pTerm' 0 (TVar x)
      <*> mapM pAlt alts
      <*> pTerm' 0 def
    where
      pAlt (TALit l b) = pAlt' <$> pTerm' 0 (TLit l) <*> pTerm' 0 b
      pAlt (TAGuard g b) =
        pAlt' <$> ((text "_" <+> text "|" <+>) <$> pTerm' 0 g)
              <*> (pTerm' 0 b)
      pAlt (TACon c a b) =
        withNames a $ \ xs -> bindNames xs $
        pAlt' <$> pTerm' 0 (TApp (TCon c) [TVar i | i <- reverse [0..a - 1]])
              <*> pTerm' 0 b
      pAlt' p b = sep [p <+> text "→", nest 2 b]

  TUnit -> pure $ text "()"
  TSort -> pure $ text "Set"
  TErased -> pure $ text "_"
  TError err -> paren 9 $ pure $ text "error" <+> text (show (show err))
