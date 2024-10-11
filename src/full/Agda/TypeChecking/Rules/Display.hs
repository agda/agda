{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rules.Display (checkDisplayPragma) where

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Internal as I
import Agda.Syntax.Common

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Warnings (warning)

import Agda.Syntax.Common.Pretty (prettyShow, render)

import Agda.Utils.Impossible

-- | Add display pragma if well-formed.
--   Otherwise, throw 'InvalidDisplayForm' warning and ignore it.
--
checkDisplayPragma :: QName -> [NamedArg A.Pattern] -> A.Expr -> TCM ()
checkDisplayPragma f ps e = do
  res <- inTopContext $ runExceptT do
    pappToTerm f id ps \n args -> do
      -- pappToTerm puts Var 0 for every variable. We get to know how many there were (n) so
      -- now we can renumber them with decreasing deBruijn indices.
      let lhs = renumberElims (n - 1) args
      Display n lhs . DTerm <$> exprToTerm e
  case res of
    Left reason -> warning $ InvalidDisplayForm f reason
    Right df -> do
      reportSLn "tc.display.pragma" 20 $ "Adding display form for " ++ prettyShow f
      reportSLn "tc.display.pragma" 90 $ ": \n  " ++ show df
      addDisplayForm f df

-- | The monad to check display forms.
--   The 'String' contains the reason to reject the display form.
--
type M = ExceptT String TCM

-- | Helper data type to record whether a pattern on the LHS contributed
-- a 'Proj' elimination or an 'Apply' elimination.
data ProjOrApp = IsProj QName | IsApp Term

patternsToTerms :: Telescope -> [NamedArg A.Pattern] -> (Int -> Elims -> M a) -> M a
patternsToTerms _ [] ret = ret 0 []
patternsToTerms EmptyTel (p : ps) ret =
  patternToTerm (namedArg p) \n v ->
  patternsToTerms EmptyTel ps \m vs -> ret (n + m) (inheritHiding p v : vs)
patternsToTerms (ExtendTel a tel) (p : ps) ret
  | fromMaybe __IMPOSSIBLE__ $ fittingNamedArg p a =
      patternToTerm (namedArg p) \n v ->
      patternsToTerms (unAbs tel) ps \m vs -> ret (n + m) (inheritHiding p v : vs)
  | otherwise =
      bindWild $ patternsToTerms (unAbs tel) (p : ps) \n vs ->
      ret (1 + n) (inheritHiding a (IsApp (Var 0 [])) : vs)

inheritHiding :: LensHiding a => a -> ProjOrApp -> Elim
inheritHiding a (IsProj q) = Proj ProjSystem q
inheritHiding a (IsApp t) = Apply (setHiding (getHiding a) (defaultArg t))

pappToTerm :: QName -> (Elims -> b) -> [NamedArg A.Pattern] -> (Int -> b -> M a) -> M a
pappToTerm x f ps ret = do
  def <- getConstInfo x
  TelV tel _ <- telView $ defType def
  let dropTel n = telFromList . drop n . telToList
      pars =
        case theDef def of
          Constructor { conPars = p } -> p
          Function { funProjection = Right Projection{projIndex = i} }
            | i > 0 -> i - 1
          _ -> 0

  patternsToTerms (dropTel pars tel) ps $ \ n vs -> ret n (f vs)

patternToTerm :: A.Pattern -> (Nat -> ProjOrApp -> M a) -> M a
patternToTerm p ret =
  case p of
    A.VarP A.BindName{unBind = x}   -> bindVar x $ ret 1 (IsApp (Var 0 []))
    A.ConP _ cs ps
      | Just c <- getUnambiguous cs -> pappToTerm c (Con (ConHead c IsData Inductive []) ConOCon) ps \n t -> ret n (IsApp t)
      | otherwise                   -> ambigErr "constructor" cs
    A.ProjP _ _ ds
      | Just d <- getUnambiguous ds -> ret 0 $ IsProj d
      | otherwise                   -> ambigErr "projection" ds
    A.DefP _ fs ps
      | Just f <- getUnambiguous fs -> pappToTerm f (Def f) ps \n t -> ret n (IsApp t)
      | otherwise                   -> ambigErr "DefP" fs
    A.LitP _ l                      -> ret 0 $ IsApp $ Lit l
    A.WildP _                       -> bindWild $ ret 1 $ IsApp (Var 0 [])
    A.AsP{}                         -> failP "an @-pattern"
    A.DotP{}                        -> failP "a dot pattern"
    A.AbsurdP{}                     -> failP "an absurd pattern"
    A.PatternSynP{}                 -> __IMPOSSIBLE__
    A.RecP{}                        -> failP "a record pattern"
    A.EqualP{}                      -> failP "a system pattern"
    A.WithP{}                       -> __IMPOSSIBLE__
  where
    fail = throwError . ("its left-hand side contains " ++)
    failP s = fail . (s ++) . (": " ++) . render =<< prettyA p
    ambigErr thing (AmbQ xs) =
      fail . render =<< do
        text ("an ambiguous " ++ thing ++ ":") <?>
          fsep (punctuate comma (fmap pretty xs))

bindWild :: M a -> M a
bindWild ret = do
  x <- freshNoName_
  bindVar x ret

bindVar :: Name -> M a -> M a
bindVar x ret = addContext x ret

exprToTerm :: A.Expr -> M Term
exprToTerm e =
  case unScope e of
    A.Var x          -> fst <$> getVarInfo x
    A.Def' f NoSuffix-> pure $ Def f []
    A.Def'{}         -> fail "suffix"
    A.Con c          -> pure $ Con (ConHead (headAmbQ c) IsData Inductive []) ConOCon [] -- Don't care too much about ambiguity here
    A.Lit _ l        -> pure $ Lit l
    A.App _ e arg    -> applyE <$> exprToTerm e <*> ((:[]) . inheritHiding arg . IsApp <$> exprToTerm (namedArg arg))

    A.Proj _ f       -> pure $ Def (headAmbQ f) []   -- only for printing so we don't have to worry too much here
    A.PatternSyn f   -> pure $ Def (headAmbQ f) []
    A.Macro f        -> pure $ Def f []

    A.WithApp{}      -> fail "with application"
    A.QuestionMark{} -> fail "hole"
    A.Underscore{}   -> fail "metavariable"
    A.Dot{}          -> fail "dotted expression"
    A.Lam{}          -> fail "lambda"
    A.AbsurdLam{}    -> fail "lambda"
    A.ExtendedLam{}  -> fail "lambda"
    A.Fun{}          -> fail "function type"
    A.Pi{}           -> fail "function type"
    A.Generalized{}  -> __IMPOSSIBLE__
    A.Let{}          -> fail "let"
    A.Rec{}          -> fail "record"
    A.RecUpdate{}    -> fail "record update"
    A.ScopedExpr{}   -> __IMPOSSIBLE__
    A.Quote{}        -> fail "quotation"
    A.QuoteTerm{}    -> fail "quotation"
    A.Unquote{}      -> fail "unquote"
    A.DontCare{}     -> __IMPOSSIBLE__
  where
    fail = throwError . ("its right-hand side contains a " ++)

renumberElims :: Nat -> Elims -> Elims
renumberElims n es = evalState (renumbers es) n
  where
    next :: State Nat Nat
    next = do i <- get; i <$ put (i - 1)

    renumbers :: Elims -> State Nat Elims
    renumbers = (traverse . traverse) renumber

    renumber :: Term -> State Nat Term
    renumber (Var 0 [])   = var <$> next
    renumber (Def f es)   = Def f <$> renumbers es
    renumber (Con c h es) = Con c h <$> renumbers es
    renumber (Lit l)      = pure $ Lit l
    renumber _            = __IMPOSSIBLE__ -- We need only handle the result of patternToTerm here
