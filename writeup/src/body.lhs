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

\begin{myhs}
\begin{code}
  data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}
\end{myhs}

  is

\begin{myhs}
\begin{code}
  REP (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}
\end{myhs}

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

\begin{myhs}
\begin{code}
class Size (a :: *) where
  size :: a -> Int
  default size  :: (Generic a , GSize (Rep a))
                => a -> Int
  size = gsize . from
\end{code}
\end{myhs}

  The default keyword instructs Haskell to use the provided
implementation whenever the constraint |(Generic a , GSize (Rep a))| 
can be satisfied. In a nutshell, we are saying that if Haskell
is aware of a generic representation for values of type |a|,
it can use the generic size function. This generic size function
is, in fact, the second piece we need to define. We will
need another class and will use the instance mechanism to encode
induction on the structure of the type:

\begin{myhs}
\begin{code}
class GSize (rep :: * -> *) where
  gsize :: rep x -> Int
instance GSize V1 where gsize _ = 0
instance GSize U1 where gsize _ = 1
instance (GSize f , GSize g) => GSize (f :*: g) where
  gsize (f :*: g) = gsize f + gsize g
instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g
\end{code}
\end{myhs}

  We still have to handle the base case for when 
  we might have an arbitrary type in a position. If we require
  this type to be an instance of |Size| we can sucessfully tie
  the recursive knot.

\begin{myhs}
\begin{code}
instance (Size a) => GSize (K1 R a) where
  gsize (K1 a) = size a
\end{code}
\end{myhs}

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
  we call \emph{opaque types}: those types that constitute the base of the universe.

  Upon reflecting on our generic |size| function we see a number of issues. Most
  notably is the amount of boilerplate to simply sum up all the sizes
  of the fields of whatever constructors make up the value. This is a direct
  consequence of not having access to the \emph{sum-of-products} structure
  that Haskell's |data| declarations follow. We will see how one could tackle that
  in Section~\ref{sec:explicitsop}. More worying, perhaps, is the fact that
  the generic representation does not carry any information about the
  recursive structure of the type. We are relying on the instance search
  mechanism to figure out that the recursive arguments can be treated
  with the default |size| function.

\TODO{%
\begin{itemize}
  \item Defining things by induction is bad. We want combinators!! \texttt{generics-sop} 
        for the rescue.
  \item \texttt{generics-sop} doesn't have explicit recursion! We fix it. Moreover,
        we encode mutual recursion. \texttt{Multirec} doesn't cut it because of
        definition by induction.
\end{itemize}}

\subsection{Explicit Sums of Products}
\label{sec:explicitsop}

\victor{With \texttt{generics-sop}~\cite{deVries2014} we can write
seomthing in the lines of the code below. Much more interesting}

\begin{myhs}
\begin{code}
gsize :: (Generic a , All2 Size (Code a)) => a -> Int
gsize  = sum
       . elim (map size)
       . from
\end{code}
\end{myhs}

\begin{itemize}
  \item No need for |GSize| class; clear combinator-based |gsize| function.
  \item Still need |Size| class.
  \item Still no explicit recursion.
\end{itemize}

\TODO{What are we going to do once we put explicit recursion
in the mix?}

\subsection{Explicit Least Fixpoints}
\label{sec:explicitfix}

\subsection{Mutually Recursive Sums of Products}
\label{sec:mrsop}

\victor{show generic equality or compos.}

\section{Encoding a Mutually Recursive Family}
\label{sec:family}

\alejandro{Driving in Manual from Gameplan}

\section{Deriving a Mutually Recursive Family}
\label{sec:templatehaskell}

\victor{Driving in Auto from Gameplan}