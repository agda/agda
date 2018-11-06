\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --no-positivity-check
            --no-termination-check
            -v 0 #-}

{-# FOREIGN GHC
  f :: Maybe Bool -> Bool
  f Nothing        = False
  f (Just  True)   = True
  f (Just  False)  = False
  #-}

postulate
  A B : Set

{-# DISPLAY A = B #-}
\end{code}

\end{document}
