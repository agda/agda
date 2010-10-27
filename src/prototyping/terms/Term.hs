
module Term where

import Text.PrettyPrint
import Pretty
import Name

data Decl = Def Name Term
          | Decl Name
  deriving Show

data Term = Var Name [Term]
          | Con Name [Term]
          | Lam Name Term
          | Closure Term Env

type Env = [(Name, Term)]

instance Show Term where
  show = show . pretty

instance Pretty Name where
  pretty (Name x n) = cat [ text x, text "_", text (show n) ]

instance Pretty Term where
  prettyPrec p v = case v of
    Var x vs -> app (pretty x) vs
    Con c vs -> app (pretty c) vs
    Lam x v  -> paren (p > 0) $ sep [ text "\\" <> pretty x <+> text "->"
                                    , nest 2 $ pretty v
                                    ]
    Closure v env ->
      sep [ brackets (pretty v)
          , nest 2 $ braces $ fsep $ punctuate (text ";") $
              [ sep [ pretty x <+> text "="
                    , nest 2 $ pretty v
                    ]
              | (x, v) <- env
              ]
          ]
    where
      app d [] = d
      app d vs = paren (p > 1) $ fsep (d : map (prettyPrec 2) vs)
