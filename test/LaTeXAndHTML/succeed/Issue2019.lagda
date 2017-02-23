\documentclass{article}
\usepackage{agda}

\begin{document}

\begin{code}
-- We use non-standard spaces between the name of the term and the
-- colon.
postulate
  s00A0 : Set  -- NO-BREAK SPACE        ("\ " with Agda input method)
  s2004 : Set  -- THREE-PER-EM SPACE    ("\;" with Agda input method)
  s202F : Set  -- NARROW NO-BREAK SPACE ("\," with Agda input method)
\end{code}

% Various whitespace characters: "    ".
\begin{code}
open import Agda.Builtin.String

-- Various whitespace characters: "    ".

various-whitespace-characters : String
various-whitespace-characters = "    "
\end{code}

\end{document}
