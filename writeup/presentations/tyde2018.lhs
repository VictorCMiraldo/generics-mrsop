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
%format (P (a)) = "\HS{''}" a
%format SOPK     = "\HS{''[ ''[}\HT{*}\HS{] ]}"
%format (PL (a)) = "\HS{''[}{" a "}\HS{]}"
%format Star     = "\HT{*}"


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
      \item Existing libraries are either hard to use or not expressive
            enough
      \pause
      \item GHC novel features allows combination of sucessful ideas
            from previous libraries
      \pause
      \item No combinator-based GP library for mutually recursive families.
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
  \pause
  \item Codes versus Pattern Functors
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
\frametitle{Pattern Functors (\texttt{GHC.Generics})}

  Defines the representation of a datatype directly:

%format :+: = "\HS{:\!\!+\!\!:}"
%format :*: = "\HS{:\!\!*\!\!:}"
\begin{code}
data Bin a   =    Leaf a 
             |    Fork (Bin a) (Bin a)

Rep (Bin a)  =    K1 a 
             :+:  (K1 (Bin a) :*: K1 (Bin a))
\end{code}
\pause
\begin{code}
data (f :+: g)  x  = L1 (f x) | R1 (g x)
data (f :*: g)  x  = f x :*: g x
data K1 a       x  = K1 x
\end{code}
\pause
Note the absence of a pattern-functor for handling recursion.
\end{frame}

\begin{frame}
\frametitle{Pattern Functors (\texttt{regular})}

  The \texttt{regular} and \texttt{multirec} have a pattern functor
for representing recursion.
\begin{code}
data I x = I x
\end{code}
Now, |Rep (Bin a) = K1 a :+: (I :*: I)|,\\
\pause
which allows for explicit least fixpoints:

%format isoto = "\mathbin{\HS{\approx}}"
|Bin a isoto Rep (Bin a) (Bin a)|

\pause
Permitting generic recursion shemes:
\begin{code}
cata :: (Rep f a -> a) -> f -> a
\end{code}
\end{frame}

\begin{frame}
\frametitle{Pattern Functors}

  Regardless of recursion, class dispatch is used
  for generic functions:

\begin{code}
class GSize (rep :: Star -> Star) where
  gsize :: rep x -> Int

instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g

dots

size :: Bin a -> Int
size = gsize . from
\end{code}
\end{frame}

\begin{frame}
\frametitle{Pattern Functors Drawbacks}

  \begin{itemize}
  \itemsep2em
    \item No guarantee about the form of |Rep|:
          \pause
          product-of-sums is valid
    \pause
    \item No guarantee about combinators used
          in |Rep|: \pause |K1 Int :+: Maybe| 
          breaks class-dispatch.
    \pause
    \item Class-dispatch fragile and hard to extend.
  \end{itemize}
\end{frame}

\begin{frame}
\frametitle{Codes (\texttt{genrics-sop})}

  \begin{itemize}
    \itemsep1em
    \item Addresses the issues with pattern-functors.
    \pause
    \item The language that representations are defined
          over.
  \end{itemize}

\begin{code}
type family     Code (a :: Star)  :: SOPK
type instance   Code (Bin a)      = PL (PL a , PL (Bin a , Bin a))
\end{code}
\pause
\begin{code}
Rep :: SOPK -> Star
\end{code}
\end{frame}
  

\begin{frame}
  \titlepage
\end{frame}

\end{document}