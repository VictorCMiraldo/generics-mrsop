\documentclass{beamer}

\usepackage{booktabs}
\usepackage{multirow}
\usepackage[all]{xy}

\usetheme{uucs}


\newcommand{\ra}[1]{\renewcommand{\arraystretch}{#1}}

%include polycode.fmt 
%include stylish.lhs


% Easy to typeset Haskell types using the \HSCon
% command from stylish.lhs (if it's defined!)
\newcommand{\HT}[1]{\ifdefined\HSCon\HSCon{#1}\else#1\fi}
\newcommand{\HS}[1]{\ifdefined\HSSym\HSSym{#1}\else#1\fi}
\newcommand{\HV}[1]{\ifdefined\HSVar\HSVar{#1}\else#1\fi}

%%% Usefull Notation
%format dots    = "\HS{\dots}"
%format forall  = "\HS{\forall}"
%format dot     = "\HS{.}"
%format ^=      = "\HS{\bumpeq}"
%format alpha   = "\HV{\alpha}"
%format phi     = "\HV{\varphi}"
%format phi1    = "\HV{\varphi_1}"
%format phi2    = "\HV{\varphi_2}"
%format kappa   = "\HV{\kappa}"
%format kappa1  = "\HV{\kappa_1}"
%format kappa2  = "\HV{\kappa_2}"
%format fSq     = "\HV{f}"
%format =~=     = "\HS{\approx}"


% ---------------------------------------------------

\title{Generic Programming for Mutually Recursive Families}
\author{Victor Cacciari Miraldo, Alejandro Serrano Mena}
\date{February 28, 2018}

\begin{document}

\begin{frame}
  \titlepage
\end{frame}

\begin{frame}
\frametitle{Generic Programming Primer}

  \begin{itemize}
    \itemsep1em
    \item<1-> Translate class of datatypes to standard representation
    \item<2-> Perform generic operation
    \item<3-> Translate back to original representation
  \end{itemize}

\vspace{1em}

\begin{overprint}
\onslide<1>\begin{displaymath}
\xymatrix@@C=4em{
  |T| \ar[r]^(.4){|from|} & |Rep T| & &
}
\end{displaymath}
\onslide<2>\begin{displaymath}
\xymatrix@@C=4em{
  |T| \ar[r]^(.4){|from|} & |Rep T| \ar[r]^{|f|} & |Rep U| & 
}
\end{displaymath}
\onslide<3>\begin{displaymath}
\xymatrix@@C=4em{
  |T| \ar[r]^(.4){|from|} & |Rep T| \ar[r]^{|f|}
                    & |Rep U| \ar[r]^{|to|}
                    & |U|
}
\end{displaymath}
\end{overprint}
\end{frame}

\begin{frame}
\frametitle{Generic Programming Shortcommings}

\begin{itemize}
\itemsep2em
  \item<1-> Class of representable datatypes
    \begin{itemize}
      \item Regular, Nested, Mutually Recursive, ...
    \end{itemize}
  \item<2-> Generic Combinators
    \begin{itemize}
      \item<3-> Expressivity
      \item<4-> Ease of use
    \end{itemize}
\end{itemize}
\end{frame}
      

\begin{frame}
\frametitle{Current Spectrum of Generic Programming}

\begin{figure}\centering
\ra{1.3}
\begin{tabular}{@@{}lll@@{}}\toprule
                        & Pattern Functors       & Codes                 \\ \midrule
  No Explicit Recursion & \texttt{GHC.Generics}  & \texttt{generics-sop} \\
  Simple Recursion      &  \texttt{regular}      &  \multirow{2}{*}{\textbf{\texttt{generics-mrsop}}} \\
  Mutual Recursion      &  \texttt{multirec}     &   \\
\bottomrule
\end{tabular}
% \mycaption{Spectrum of static generic programming libraries}
% \label{fig:gplibraries}
\end{figure}
\end{frame}

\begin{frame}
\frametitle{Pattern Functors versus Codes}
\begin{block}{Pattern Functors}
\vspace{-.5em}
\begin{code}
type Rep :: Star -> Star
\end{code}
\vspace{-2em}
\begin{itemize}
  \item<2-> Generic Functions by Class-dispatch
  \item<3-> Not every |T :: Star| has a |Rep|
\end{itemize}
\end{block}
\vspace{-.5em}
\begin{block}{Codes}
\vspace{-.5em}
\begin{code}
data Codes = dots
type Rep :: Codes -> Star
\end{code}
\vspace{-2em}
\begin{itemize}
  \item<2-> Generic functions by induction on |Codes|
  \item<3-> |Codes| is a closed universe
\end{itemize}
\end{block}
\end{frame}

\begin{frame}
  \titlepage
\end{frame}

\end{document}