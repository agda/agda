
module Agda.TypeChecking.Rules.Display (checkDisplayPragma) where

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

import Agda.Utils.Pretty (prettyShow)

import Agda.Utils.Impossible

checkDisplayPragma :: QName -> [NamedArg A.Pattern] -> A.Expr -> TCM ()
checkDisplayPragma f ps e = do
  df <- inTopContext $ do
          pappToTerm f id ps $ \ n args -> do
            -- pappToTerm puts Var 0 for every variable. We get to know how many there were (n) so
            -- now we can renumber them with decreasing deBruijn indices.
            let lhs = renumberElims (n - 1) $ map I.Apply args
            v <- exprToTerm e
            return $ Display n lhs (DTerm v)
  reportSLn "tc.display.pragma" 20 $ "Adding display form for " ++ prettyShow f ++ "\n  " ++ show df
  addDisplayForm f df

--UNUSED Liang-Ting 2019-07-16
---- Compute a left-hand side for a display form. Inserts implicits, but no type
---- checking so does the wrong thing if implicitness is computed. Binds variables.
--displayLHS :: Telescope -> [NamedArg A.Pattern] -> (Int -> [Term] -> TCM a) -> TCM a
--displayLHS tel ps ret = patternsToTerms tel ps $ \n vs -> ret n (map unArg vs)

type ToTm = StateT Nat TCM

patternsToTerms :: Telescope -> [NamedArg A.Pattern] -> (Int -> Args -> TCM a) -> TCM a
patternsToTerms _ [] ret = ret 0 []
patternsToTerms EmptyTel (p : ps) ret =
  patternToTerm (namedArg p) $ \n v ->
  patternsToTerms EmptyTel ps     $ \m vs -> ret (n + m) (inheritHiding p v : vs)
patternsToTerms (ExtendTel a tel) (p : ps) ret
  -- Andreas, 2019-07-22, while #3353: we should use domName, not absName !!
  -- WAS: -- | sameHiding p a, visible p || maybe True (absName tel ==) (bareNameOf p) =  -- no ArgName or same as p
  | fromMaybe __IMPOSSIBLE__ $ fittingNamedArg p a =
      patternToTerm (namedArg p) $ \n v ->
      patternsToTerms (unAbs tel) ps  $ \m vs -> ret (n + m) (inheritHiding p v : vs)
  | otherwise =
      bindWild $ patternsToTerms (unAbs tel) (p : ps) $ \n vs ->
      ret (1 + n) (inheritHiding a (Var 0 []) : vs)

inheritHiding :: LensHiding a => a -> b -> Arg b
inheritHiding a b = setHiding (getHiding a) (defaultArg b)

pappToTerm :: QName -> (Args -> b) -> [NamedArg A.Pattern] -> (Int -> b -> TCM a) -> TCM a
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

patternToTerm :: A.Pattern -> (Nat -> Term -> TCM a) -> TCM a
patternToTerm p ret =
  case p of
    A.VarP A.BindName{unBind = x}   -> bindVar x $ ret 1 (Var 0 [])
    A.ConP _ cs ps
      | Just c <- getUnambiguous cs -> pappToTerm c (Con (ConHead c IsData Inductive []) ConOCon . map Apply) ps ret
      | otherwise                   -> ambigErr "constructor" cs
    A.ProjP _ _ ds
      | Just d <- getUnambiguous ds -> ret 0 (Def d [])
      | otherwise                   -> ambigErr "projection" ds
    A.DefP _ fs ps
      | Just f <- getUnambiguous fs -> pappToTerm f (Def f . map Apply) ps ret
      | otherwise                   -> ambigErr "DefP" fs
    A.LitP _ l                      -> ret 0 $ Lit l
    A.WildP _                       -> bindWild $ ret 1 (Var 0 [])
    _ -> genericDocError =<< vcat [ "Pattern not allowed in DISPLAY pragma:", prettyA p ]
  where
    ambigErr thing (AmbQ xs) =
      genericDocError =<< do
        text ("Ambiguous " ++ thing ++ ":") <?>
          fsep (punctuate comma (fmap pretty xs))

bindWild :: TCM a -> TCM a
bindWild ret = do
  x <- freshNoName_
  bindVar x ret

bindVar :: Name -> TCM a -> TCM a
bindVar x ret = addContext x ret

exprToTerm :: A.Expr -> TCM Term
exprToTerm e =
  case unScope e of
    A.Var x  -> fst <$> getVarInfo x
    A.Def f  -> pure $ Def f []
    A.Con c  -> pure $ Con (ConHead (headAmbQ c) IsData Inductive []) ConOCon [] -- Don't care too much about ambiguity here
    A.Lit _ l  -> pure $ Lit l
    A.App _ e arg  -> apply <$> exprToTerm e <*> ((:[]) . inheritHiding arg <$> exprToTerm (namedArg arg))

    A.Proj _ f -> pure $ Def (headAmbQ f) []   -- only for printing so we don't have to worry too much here
    A.PatternSyn f -> pure $ Def (headAmbQ f) []
    A.Macro f      -> pure $ Def f []

    A.WithApp{}      -> notAllowed "with application"
    A.QuestionMark{} -> notAllowed "holes"
    A.Underscore{}   -> notAllowed "metavariables"
    A.Lam{}          -> notAllowed "lambdas"
    A.AbsurdLam{}    -> notAllowed "lambdas"
    A.ExtendedLam{}  -> notAllowed "lambdas"
    _                -> typeError $ GenericError $ "TODO: exprToTerm " ++ show e
  where
    notAllowed s = typeError $ GenericError $ "Not allowed in DISPLAY pragma right-hand side: " ++ s

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
