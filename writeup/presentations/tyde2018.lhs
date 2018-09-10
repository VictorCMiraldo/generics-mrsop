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
%format (LIST (a)) = "\HS{[}" a "\HS{]}"
%format space  = "\vspace{1em}"
%format EMPTYL = "\HS{''[]}"
%format LISTKS = "\HS{[}" k "\HS{]}"
%format isoto = "\mathbin{\HS{\approx}}"
%format :*: = "\HS{:\!\!*\!\!:}"
%format :+: = "\HS{:\!\!+\!\!:}"



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
      \item No combinator-based GP library for mutually recursive families
      \pause
      \item GHC novel features allows combination of sucessful ideas
            from previous libraries
    \end{itemize}
  \end{block}
\pause
  \begin{block}{Goal}
    Design and implement a ``user-friendly'' GP library for handling mutually recursive
    families
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
Note the absence of a pattern functor for handling recursion.
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
\frametitle{Codes (\texttt{generics-sop})}

  \begin{itemize}
    \itemsep1em
    \item Addresses the issues with pattern functors.
    \pause
    \item The language that representations are defined
          over.
  \end{itemize}

\begin{code}
data Bin a   =    Leaf a 
             |    Fork (Bin a) (Bin a)

type family     Code (a :: Star)  :: SOPK
type instance   Code (Bin a)      = PL (PL a , PL (Bin a , Bin a))
\end{code}
\end{frame}

\begin{frame}
\frametitle{Interpreting Codes (\texttt{generics-sop})}

  Start with n-ary sums and products:
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
\end{code}

  \pause
  Define the representation:

\begin{code}
type Rep = NS (NP I) :: SOPK -> Star
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Interpreting Codes (\texttt{generics-sop})}
\begin{code}
type Rep = NS (NP I) :: SOPK -> Star

data Bin a   =    Leaf a 
             |    Fork (Bin a) (Bin a)

\end{code}
\pause
Recall the |Tree| example:
\begin{code}
type instance   Code (Bin a)      = PL (PL a , PL (Bin a , Bin a))

leaf     :: a -> Rep (Code (Tree a))
leaf e   = Here (Cons e Nil)

bin      :: Tree a -> Tree a -> Rep (Code (Tree a))
bin l r  = There (Here (Cons l (Cons r Nil)))
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Generic Functionality (\texttt{generics-sop})}

  Codes allow for combinators instead of class-dispatch:

\begin{code}
elimNP :: (forall k dot f k -> a) -> NP f xs -> LIST a
elimNS :: (forall k dot f k -> a) -> NS f xs -> a
\end{code}
\vspace{-1.5em}
\pause
\begin{code}
class Size a where 
  size :: a -> Int
space
gsize :: (Generic a, All2 Size (Code a)) => a -> Int
gsize = succ . sum . elimNS (elimNP (size . unI)) . from
  where unI (I x) = x
\end{code}
\pause
Still: no explicit recursion: typeclass and complicated constraints.
\end{frame}

\newcommand{\mrsopName}{\textbf{\texttt{generics-mrsop}}}
\begin{frame}
  \frametitle{Mutual Recursion (\mrsopName)}
\vspace{-2em}
\begin{overprint}
\onslide<1>%
Start with |Rep| as before:
\onslide<2>%
Add codes to handle a single recursive position:
\onslide<3>%
Augment codes to have $n$ recursive positions:
\end{overprint}
\begin{overprint}
\onslide<1>%
\begin{code}
data I x = I x 
space
space
space
space
type Rep (f :: SOPK) 
  = NS (NP I) f 
\end{code}
\onslide<2>%
\begin{code}
data Atom = I | KInt | dots
data NA :: Star -> Atom -> Star where
  NA_I  :: x    -> NA x I
  NA_K  :: Int  -> NA x KInt
space   
type Rep (x :: Star) (f :: (P (LIST (P (LIST Atom)))))  
  = NS (NP (NA x)) f
\end{code}
\onslide<3>%
\begin{code}
data Atom = I Nat | KInt | dots
data NA :: (Nat -> Star) -> Atom -> Star where
  NA_I  :: x n  -> NA x (I n)
  NA_K  :: Int  -> NA x KInt
space
type Rep (x :: Nat -> Star) (f :: (P (LIST (P (LIST Atom)))))  
  = NS (NP (NA x)) f
\end{code}
\end{overprint}
\end{frame}

\begin{frame}
  \frametitle{Example (\mrsopName)}

%format pause = "\pause"
\begin{code}
data RTree a   = RTree a (Forest a)
data Forest a  = Nil | Cons (RTree a) (Forest a)
space
type Fam    = PL (RTree Int, Forest Int)
\end{code} 
\pause
\begin{code}
type CodeRTree   = PL (PL (KInt , I 1)) 
type CodeForest  = PL (EMPTYL , PL (I 0 , I 1))
type Codes  = PL (CodeRTree , CodeForest)
\end{code} 
\pause
\begin{code}
instance Family Fam Codes where
  dots
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Closing the Recursive Knot (\mrsopName)}
\vspace{-1em}
  \begin{itemize}
    \item Define a family: |fam :: PL Star|
    \pause
    \item Define its codes: |codes :: PL (PL (PL Atom))|
    \pause
    \item Define lookup:
  \end{itemize}
\begin{code}
type family Lkup (ls :: PL k) (n :: Nat) :: k where
  Lkup EMPTYL          _      = TypeError "Out of bounds"
  Lkup (x (P (:)) xs)  Z      = x
  Lkup (x (P (:)) xs)  (S n)  = Lkup xs n
\end{code}
\pause
Then, finally, the $i$-th type is represented by:
\begin{code}
Rep (Lkup fam) (Lkup i codes)
\end{code}
\pause |Lkup| can't be partially applied though.
\end{frame}

\begin{frame}
  \frametitle{Wrapping it up (\mrsopName)}

  Create an |El| type to be able to partially apply it
and wrap it all in a typeclass:
\pause
\begin{code}
data El :: PL Star -> Nat -> Star where
  El :: Lkup fam ix -> El fam ix
space
class Family (fam :: PL Star) (codes :: PL (PL (PL Atom))) where
  from  :: SNat ix
        -> El fam ix
        -> Rep (El fam) (Lkup codes ix)
  to    :: SNat ix
        -> Rep (El fam) (Lkup codes ix)
        -> El fam ix
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Well formed Representations Only}

  \begin{itemize}
    \itemsep1em
    \item The |data Atom = I Nat || dots| type might seem too
          permissive
    \pause
    \item One solution: | data Atom n = I (Fin n) || dots|\\
          Too complicated in Haskell.
    \pause
    \item In fact, there is no problem: one could define:
          |type CodeRTree = (PL (PL (KInt , I 42)))|, 
          the instance would be impossible to write.
    \pause
    \item Malformed codes $\Rightarrow$ uninhabitable representations.
    \item Errors are caught at compile time.
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Deep versus Shallow}

  Deep encoding comes for free!
\begin{code}
newtype Fix codes ix
  = Fix (Rep (Fix codes) (Lkup codes ix))
\end{code}
\vspace{-2em}
\pause
\begin{code}
deep  :: (Family fam codes) 
      => El fam ix -> Fix codes ix
deep  = Fix . mapRep deep . from
\end{code}
\vspace{-2em}
\pause
  \begin{itemize}
    \item provide recursion schemes (|cata|, |ana|, |synthesize|, etc)
    \item No need to carry constraints around
  \end{itemize}
\vspace{-1em}
\pause
\begin{code}
gsize  :: (Family fam codes)
       => El fam ix -> Int
gsize  = cata (succ . sum . elimNP (elimNA id)) . deep
\end{code}
\end{frame}

\begin{frame}
\frametitle{Custom Opaque Types}

\begin{overprint}
\onslide<1>
Recall our definition of |Atom|:
\onslide<2->
Add another parameter to it:
\end{overprint}

\begin{overprint}
\onslide<1>%
\begin{code}
data Atom = I Nat | KInt | dots
data NA  :: (Nat -> Star) -> Atom 
         -> Star where
  NA_I  :: x n  -> NA x (I n)
  NA_K  :: Int  -> NA x KInt
\end{code}
\onslide<2->%
\begin{code}
data Atom kon = I Nat | K kon 
data NA  :: (kon -> Star) -> (Nat -> Star) -> Atom kon 
         -> Star where
  NA_I  :: x   n  -> NA ki x (I n)
  NA_K  :: ki  k  -> NA ki x (K k)
\end{code}
\end{overprint}

\onslide<3->{
Define a kind for opaque types and their interpretation:

\begin{code}
data Opaque = O_Int | O_Float
data OpaqueSingl :: Opaque -> Star where
  OS_Int    :: Int    -> OpaqueSingl O_Int
  OS_Float  :: Float  -> OpaqueSingl O_Float
\end{code}
}

\end{frame}

\begin{frame}
  \frametitle{Other Features from \texttt{generics-mrsop}}

  \begin{itemize}
    \itemsep2em
    \item Custom opaque types.
    \pause
    \item Zippers for mutually recursive families.
    \pause
    \item Automatic |Family| generation with Template Haskell.
    \pause
    \item Metadata support inspired by \texttt{generics-sop}.
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Lessons and Discussion}
  \begin{itemize}
    \itemsep2em
    \item Found two bugs in GHC: \#14987 and \#15517 (closed) 
    \pause
    \item Working with deep representations is simpler:
      \begin{itemize}
        \item Recursion schemes
        \item No need to carry constraints around
      \end{itemize}
    \pause
    \item Very powerful tool to work with generic AST's
    \pause
    \item Curious about handling GADTs?\\ 
          Join Haskell Symposium tomorrow at 9h30!
  \end{itemize}
\end{frame}

\begin{frame}[plain,c]
  \frametitle{Conclusions}
\begin{center}
\emph{ \Huge Use it and Hack it! }
\texttt{https://hackage.haskell.org/package/generics-mrsop}
\end{center}
\end{frame}


\begin{frame}
  \titlepage
\end{frame}

\end{document}