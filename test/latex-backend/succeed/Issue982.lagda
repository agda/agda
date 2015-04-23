% Testing with Ubuntu 12.04.

% This version of Ubuntu uses an outdated TeX Live 2009. For testing
% this issue it is necessary to install the following packages:

%  sudo add-apt-repository ppa:texlive-backports/ppa -y
%  sudo apt-get update
%  sudo apt-get install texlive
%  sudo apt-get install texlive-latex-extra
%  sudo apt-get install texlive-xetex
%  sudo apt-get install texlive-math-extra
%  sudo apt-get install texlive-fonts-extra

\documentclass{article}

\usepackage{agda}

\begin{document}

%\renewcommand{\AgdaIndent}{\;\;}

\begin{code}
record Sigma (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Sigma public
\end{code}

\begin{code}
uncurry : {A : Set} {B : A → Set} {C : Sigma A B → Set} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Sigma A B) → C p)
uncurry f (x , y) = f x y
\end{code}

\end{document}
