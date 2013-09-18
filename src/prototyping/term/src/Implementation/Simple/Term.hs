{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Implementation.Simple.Term where

import Types.Abs
import Syntax.Abstract (Name)
import Syntax.Abstract.Pretty
import Data.Hashable
import Text.PrettyPrint

newtype Term = Term { termView :: TermView }
  deriving (Eq)

type Type = Term

data TermView = Lam (Abs Term)
              | Pi Term (Abs Term)
              | Equal Term Term Term
              | App Head [Elim]
              | Set
  deriving (Eq)

type Var = Int
data Head = Var Var
          | Def Name
          | Con Name
          | Meta MetaVar
  deriving (Eq)

var :: Var -> TermView
var x = App (Var x) []

newtype MetaVar = MetaId Integer
  deriving (Show, Eq, Ord, Hashable)

type Field = Int
data Elim = Apply Term
          | Proj Field
  deriving (Eq)

data Clause = Clause [Pattern] Term
  deriving Show

data Pattern = VarP
             | ConP Name [Pattern]
  deriving (Eq)

-- Pretty printing --------------------------------------------------------

instance Show TermView where showsPrec = defaultShow
instance Show Term     where showsPrec = defaultShow
instance Show Head     where showsPrec = defaultShow
instance Show Pattern  where showsPrec = defaultShow
instance Show Elim     where showsPrec = defaultShow

instance Pretty Elim where
  prettyPrec p (Apply e) = prettyPrec p e
  prettyPrec _ (Proj x)  = text $ "." ++ show x

instance Pretty Term where
  prettyPrec p (Term v) = prettyPrec p v

instance Pretty TermView where
  prettyPrec p e = case e of
    Set         -> text "Set"
    Equal a x y -> prettyApp p (text "_==_") [a, x, y]
    Pi a b      ->
      mparens (p > 0) $
        sep [ parens (text (absName b ++ " :") <+> pretty a) <+> text "->"
            , nest 2 $ pretty (absBody b) ]
    Lam b ->
      mparens (p > 0) $
      sep [ text ("\\" ++ absName b ++ " ->")
          , nest 2 $ pretty (absBody b) ]
    App h es -> prettyApp p (pretty h) es

instance Pretty Head where
  pretty h = case h of
    Var i -> text $ show i
    Def f -> pretty f
    Con c -> pretty c
    Meta m -> pretty m

instance Pretty MetaVar where
  pretty (MetaId i) = text ("_" ++ show i)

instance Pretty Pattern where
  prettyPrec p e = case e of
    VarP      -> text "_"
    ConP c es -> prettyApp p (pretty c) es
