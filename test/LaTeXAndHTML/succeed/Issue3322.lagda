% Nisse, 2018-10-26
% Testing that record field are already highlighted by scope checker.

\documentclass{article}

\usepackage{agda}

% This redefinition of AgdaField,
% in combination with the math-only command \bot,
% will fail the LaTeX build if no highlighting
% of fields has been performed.

\renewcommand{\AgdaField}[1]{\ensuremath{#1}}

\usepackage{amsmath}
\usepackage{newunicodechar}
\newunicodechar{₁}{\ensuremath{{}_{\text{1}}}}
\newunicodechar{₂}{\ensuremath{{}_{\text{2}}}}
\newunicodechar{⊥}{\bot}

\pagestyle{empty}

\begin{document}

\begin{code}
record R : Set₂ where
  field
    ⊥ : Set₁

r : R

r = record { ⊥ = Set }
\end{code}

\end{document}
