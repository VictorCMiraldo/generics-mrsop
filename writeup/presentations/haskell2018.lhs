\documentclass{beamer}

\usetheme{uucs}

\newcommand{\ra}[1]{\renewcommand{\arraystretch}{#1}}

%include polycode.fmt 
%include stylish.lhs


% Easy to typeset Haskell types using the \HSCon
% command from stylish.lhs (if it's defined!)
\newcommand{\HT}[1]{\ifdefined\HSCon\HSCon{#1}\else#1\fi}
\newcommand{\HS}[1]{\ifdefined\HSSym\HSSym{#1}\else#1\fi}
\newcommand{\HV}[1]{\ifdefined\HSVar\HSVar{#1}\else#1\fi}

% ---------------------------------------------------

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
%format (LIST (a)) = "\HS{[}" a "\HS{]}"
%format space  = "\vspace{1em}"
%format EMPTYL = "\HS{''[]}"
%format LISTKS = "\HS{[}" k "\HS{]}"
%format isoto = "\mathbin{\HS{\approx}}"
%format :*: = "\HS{:\!\!*\!\!:}"
%format :+: = "\HS{:\!\!+\!\!:}"

\title{Generic Programming of All Kinds}
\author{Alejandro Serrano Mena, Victor Cacciari Miraldo}
\date{February 28, 2018}

\begin{document}

\begin{frame}
  \titlepage
\end{frame}

\begin{frame}
  \frametitle{Motivation}

  \begin{itemize}
    \itemsep2em
    \item GHC's modern extensions allow for more expressive
          generic programming.

    \pause
    \item Inability to currently handle arbitrarily kinded
          datatypes.

    \pause
    \item GADTs are becomming more common: |deriving| clauses
          would be handy.
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Representing Datatypes}

  Haskell datatypes come in \emph{sums-of-products} shape:
\begin{code}
data Tree a = Leaf | Bin a (Tree a) (Tree a)
\end{code}
\pause
  Our \emph{codes} will follow that structure:
\begin{code}
type family Code (x :: Star) :: PL (PL Star)
type instance Code (Tree a) = PL (EMPTYL , PL (a , Tree a , Tree a))
\end{code}
\end{frame}


\begin{frame}
  \frametitle{Interpreting Representations}

   Must convert a |Code a| into a term of kind |Star|.
\pause
\begin{code}
data NS :: (k -> Star) -> LISTKS -> Star where
  Here   :: f x      -> NS f (x (P (:)) xs)
  There  :: NS f xs  -> NS f (x (P (:)) xs)
space
data NP :: (k -> Star) -> LISTKS -> Star where
  Nil   ::                    NP f EMPTYL
  Cons  :: f x -> NP f xs ->  NP f (x (P (:)) xs)
space
data I x = I x 
space
type SOP (c :: PL (PL Star)) = NS (NP I) c
\end{code}

\end{frame}


\begin{frame}
  \frametitle{generics-sop}

  start on |NS| and |NP|

  ppl might not be familiar with this black magic!

  show |gsize|!
\end{frame}

\begin{frame}
  \frametitle{Enlarging the language of types!}

  show figure 2!

  examples!
\end{frame}

\begin{frame}
  \frametitle{Applying type-level types to types!}

  Show |Ty|, and how it interprets |Atom| into a star for us.

  Show the |Generic| type-class and mention the existence of |ApplyT|
  and why you need such monster

\end{frame}

\begin{frame}
  \frametitle{Wait?! type-in-type?}

\end{frame}

\begin{frame}
  \frametitle{Constraints}

\end{frame}

\begin{frame}
  \frametitle{Generic GADT}


  limitations: |forall k (a :: k)| can't be represented by us
\end{frame}

\begin{frame}
  \frametitle{Arity-generic fmap }

\end{frame}


\begin{frame}
  \frametitle{Lessons discussion and conc}

  \begin{itemize}
    \item Existentials are not a problem; check paper
    \item Explicit recursion is not a problem unless you take fixpoints; check the paper
    \item Mutual recursion? No biggie! MRSOP!
  \end{itemize}

  Conclusion: We rock!

\end{frame}

\begin{frame}
  \titlepage
\end{frame}

\end{document}