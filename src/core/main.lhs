\documentclass{article} 
%include polycode.fmt 
\framedhs
%%include lhs2TeX.fmt
%%include polytt.fmt
\input{ttinit}
\input{ttinitmore}
\renewcommand{\Varid}[1]{\mathsf{#1}}% or rm for serif
\renewcommand{\Conid}[1]{\mathsf{#1}}% or rm for serif
\newcommand{\Val}{\mathbf{Val}}
\newcommand{\Set}{\mathbf{Set}}
\newcommand{\Fun}{\mathbf{Fun}}
\newcommand{\App}{\mathbf{App}}
\newcommand{\Hh}{\mathbf{H}}
\begin{document}
\include{overview} 
%include Decl.lhs
%include Check.lhs
%include Exp.lhs
%include Val.lhs
%include Conv.lhs
%include Cont.lhs
\end{document}