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
\frametitle{Motivation}

  \begin{block}{Why another generic programming library?}
    \begin{itemize}
      \itemsep2em
      \pause
      \item Existing libraries: either hard or not expressive
            enough
      \pause
      \item GHC novel features: combine sucessful ideas
            from previous libraries
      \pause
      \item Mutually recursive families are common
    \end{itemize}
  \end{block}

\end{frame}

\begin{frame}
\frametitle{Generic Programming Primer}

  \begin{itemize}
    \itemsep1em
    \item<1-> Translate class of datatypes to uniform representation
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
\onslide<3->\begin{displaymath}
\xymatrix@@C=4em{
  |T| \ar[r]^(.4){|from|} & |Rep T| \ar[r]^{|f|}
                    & |Rep U| \ar[r]^{|to|}
                    & |U|
}
\end{displaymath}
\end{overprint}
\onslide<4>
\begin{code}
class Generic t where
  from  :: t      -> Rep t
  to    :: Rep t  -> t
\end{code}
\end{frame}

\begin{frame}
\frametitle{The Design Space}

\begin{itemize}
\itemsep2em
  \item Class of representable datatypes
    \begin{itemize}
      \item Regular, Nested, Mutually Recursive, ...
    \end{itemize}
  \pause
  \item Representation of Recursion
    \begin{itemize}
      \item Implicit versus Explicit
    \end{itemize}
\end{itemize}

\pause
These choices determine the flavour of generic functions:
    \begin{itemize}
      \item Expressivity
      \item Ease of use
    \end{itemize}
\end{frame}
      

\begin{frame}
\frametitle{The Landscape}

\begin{figure}\centering
\ra{1.3}
\begin{tabular}{@@{}lll@@{}}\toprule
                        & Pattern Functors       & Codes                 \\ \midrule
  No Explicit Recursion & \texttt{GHC.Generics}  & \texttt{generics-sop} \\
  Simple Recursion      &  \texttt{regular}      &  \multirow{2}{*}{\textbf{\texttt{generics-mrsop}}} \\
  Mutual Recursion      &  \texttt{multirec}     &   \\
\bottomrule
\end{tabular}
\end{figure}
\end{frame}

\begin{frame}
\frametitle{Pattern Functors}

  Used by \texttt{GHC.Generics}, \texttt{regular}, \texttt{multirec}.

  \pause

  Defines the representation of a datatype directly:

%format :+: = "\HS{:\!\!+\!\!:}"
%format :*: = "\HS{:\!\!*\!\!:}"
\begin{code}
data Bin a = Leaf a | Fork (Bin a) (Bin a)
\end{code}
\begin{code}
Rep (Bin a)  =    K1 R a 
             :+:  (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}

\end{frame}


\begin{frame}
\frametitle{Pattern Functors}

  Class dispatch for generic functions:

\begin{code}
class GSize (rep :: * -> *) where
  gsize :: rep x -> Int

instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g

dots

size :: Bin a -> Int
size = gsize . from
\end{code}
\vspace{-2em}
\pause
\begin{block}{Issue:}
  No guarantee about the form of the |Rep|. 
  |K1 R Int :+: Maybe| is a valid |Rep|
\end{block}

\end{frame}


\begin{frame}
  \titlepage
\end{frame}

\end{document}