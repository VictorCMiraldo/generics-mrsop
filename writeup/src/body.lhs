\section{Introduction}
\label{sec:introduction}

\victor{We can talk dierctly here}

\alejandro{Like this}

\warnme{this requires attention}

\TODO{this will be done}

\tmp{this will be removed}

\section{Generic Programming in Haskell}
\label{sec:genericprog}

\victor{where should we add the following:\\
  The generic representation of

\begin{code}
  data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}

  is

\begin{code}
  PF (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}

  which is isomorphic to |Either a (Bin a , Bin a)|

}

  Since version $7.2$, GHC supports some basic generic
programming using \texttt{GHC.Generics}~\cite{Magalhaes2010}, 
which exposes the \emph{pattern functor} of a datatype. This
allows one to define a function for any datatype by induction
on \emph{pattern functors}. Defining a generic |size| function,
that provides a measure of the value in question is done in two
steps. First, we define a class that exposes a |size| function
for values in kind |*|:

\begin{code}
class Size (a :: *) where
  size :: a -> Int
  default size  :: (Generic a , GSize (PF a))
                => a -> Int
  size = gsize . from
\end{code}

  The default keyword instructs Haskell to use the provided
  implementation whenever the constraint |(Generic a , GSize (PF a))| 
  can be satisfied. In a nutshell, we are saying that if Haskell
  is aware of a generic representation for values of type |a|,
  it can use the generic size function. This generic size function
  is, in fact, the second piece we need to define. We will
  need another class and will use the instance mechanism to encode
  induction on the structure of the type:

\begin{code}
class GSize (pf :: * -> *) where
  gsize :: pf x -> Int
instance GSize V1 where gsize _ = 0
instance GSize U1 where gsize _ = 1
instance (GSize f , GSize g) => GSize (f :*: g) where
  gsize (f :*: g) = gsize f + gsize g
instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g
\end{code}

  We still have to handle the base case for when 
  we might have an arbitrary type in a position. If we require
  this type to be an instance of |Size| we can sucessfully tie
  the recursive knot.

\begin{code}
instance (Size a) => GSize (K1 R a) where
  gsize (K1 a) = size a
\end{code}

  In order to have a fully usable generic size function, one only
  needs to provide a couple of instances of |Size| for some builtin 
  Haskell types to act as a base case. We can see this if we try to
  compute |size (Bin (Leaf 1) (Leaf 2))|:

\begin{align*}
  |size (Bin (Leaf 1) (Leaf 2))| 
    &= |gsize (from (Bin (Leaf 1) (Leaf 2)))| \\
    &= |gsize (R1 (K1 (Leaf 1) :*: K1 (Leaf 2)))| \\
    &= |gsize (K1 (Leaf 1)) + gsize (K1 (Leaf 2))| \\
    &= |size (Leaf 1) + size (Leaf 2)|\\
    &= |gsize (from (Leaf 1)) + gsize (from (Leaf 2))|\\
    &= |gsize (L1 (K1 1)) + gsize (L1 (K1 2))|\\
    &= |size (1 :: Int) + size (2 :: Int)|   
\end{align*}

  Were we a compiler, we would hapilly issue a \texttt{No instance for (Size Int)} error
  message at this point. Nevertheless, the literals of type |Int| illustrate what
  we call the opaque or konstant types: those types for which we require explicit
  base cases. 
  \victor{I prefer the 'opaque' denomination, it does not require a typo. $\ddot\smile$}

\TODO{%
\begin{itemize}
  \item Defining things by induction is bad. We want combinators!! \texttt{generics-sop} 
        for the rescue.
  \item \texttt{generics-sop} doesn't have explicit recursion! We fix it. Moreover,
        we encode mutual recursion. \texttt{Multirec} doesn't cut it because of
        definition by induction.
\end{itemize}}

\victor{show generic equality or compos.}

\section{Encoding a Mutually Recursive Family}
\label{sec:family}

\alejandro{Driving in Manual from Gameplan}

\section{Deriving a Mutually Recursive Family}
\label{sec:templatehaskell}

\victor{Driving in Auto from Gameplan}