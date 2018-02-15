\section{Introduction}
\label{sec:introduction}

\victor{Mention that \texttt{Multirec} exists, but falls short just like \texttt{GHC.Generic}.
Mention we will only show the \texttt{GHC.Generics} example to keep it simple}

\section{Background}
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
on \emph{pattern functors}. 

\victor{Do I have to explain pattern-functors here?}

Defining a generic |size| function,
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

%format :*: = ":\!*\!:"
%format :+: = ":\!+\!:"
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
    &= |size (Leaf 1) + size (Leaf 2)| \tag{$\dagger$}\\
    &= |gsize (from (Leaf 1)) + gsize (from (Leaf 2))|\\
    &= |gsize (L1 (K1 1)) + gsize (L1 (K1 2))|\\
    &= |size (1 :: Int) + size (2 :: Int)|   
\end{align*}

  Were we a compiler, we would hapilly issue a \texttt{"No instance for (Size Int)"} error
message at this point. Nevertheless, the literals of type |Int| illustrate what
we call \emph{opaque types}: those types that constitute the base of the universe.

  One interesting aspect we should note here is the clearly \emph{shallow} encoding
that |from| provides. That is, we only represent \emph{one layer} of recursion
at a time. For example, in $(\dagger)$, after unwrapping the calculation of the first
\emph{layer}, we are back to having to calculate |size| for |Bin Int|, not their 
representation.

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

  Had we had access to a representation of the \emph{sum-of-products} 
structure of |Bin|, we could have defined our |gsize| function as we
described it before: sum up the sizes of the fields inside a value, ignoring
the constructor. In fact, the \texttt{generics-sop}~\cite{deVries2014} library
does precisely that. It could let us write the (simplified) |gsize| functions as:

\begin{myhs}
\begin{code}
gsize :: (Generic a) => a -> Int
gsize  = sum . elim (map size) . from
\end{code}
\end{myhs}

  Ignoring the details of the new |gsize| for a moment and focusing
on the high level structure. Remembering that |from| now
returns a \emph{sum-of-products} view over the data, akin to a list of lists, 
we can make use of an eliminator, |elim|, do apply a function to the fields
of whatever constructor it receives, it so happens that we want to recursively
compute their sizes.

  As we hinted earlier, the generic representation consists in 
a list of lists of types. The outer list represents the 
constructors of a type, and will be interpreted as a $n$-ary sum, whereas
the inner lists are interepreted as the fields of the respective constructors,
interpreted as $n$-ary products.

%format (P (a)) = "\HSSym{''}" a
\begin{myhs}
\begin{code}
type family    Code (a :: *) :: P ([ (P [*]) ])

type instance  Code (Bin a) = P ([ P [a] , P ([Bin a , Bin a]) ])
\end{code}
\end{myhs}

%format dots = "\HSSym{\cdots}"
  We then intrepret these |Code|s using $n$-ary sums of $n$-ary products of
atoms. An $n$-ary sum |NS f [k1 , k2 , dots]|
is isomorphic to |Either (f k1) (Either (f k2) dots)|, it can easily be defined using a
GADT~\cite{Xi2003}:

\begin{myhs}
\begin{code}
data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k (P (:)) ks)
  There  :: NS f ks  -> NS f (k (P (:)) ks)
\end{code}
\end{myhs}

  The $n$-ary products on the other hand resemble an heterogeneous list. Here,
|NP f [k1 , k2 , dots]| is isomorphic to |(f k1 , f k2 , dots)|. 

%format :* = "\HSCon{\times}"
\begin{myhs}
\begin{code}
data NP :: (k -> *) -> [k] -> * where
  NP0  ::                    NP f (P [])
  :*   :: f x -> NP f xs ->  NP f (x (P (:)) xs)
\end{code}
\end{myhs}

  Finally, since our atoms are of kind |*|, we can use the identity
functor, |I|, to interpret those and can finally define the representation
of values of a type |a| under the \emph{SOP} view:

\begin{myhs}
\begin{code}
type Rep a = NS (NP I) (Code a)

newtype I (a :: *) = I { unI :: a }
\end{code}
\end{myhs}

%format forall = "\HSSym{\forall}"
%format dot    = "\HSSym{.}"
  Revisiting the |gsize| example above we see that the |map| we used has
type |(forall k dot f k -> a) -> NP f ks -> [a]|, and can be defined
analogously to the the sum eliminator |elim|:

\begin{myhs}
\begin{code}
elim :: (forall k dot f k -> a) -> NS f ks -> a
elim f (Here   x)  = f x
elim f (There  x)  = elim f x
\end{code}
\end{myhs}

  We refer the reader to the original paper~\cite{deVries2014} for a
more comprehensive explanation of the \texttt{generics-sop} library.

  Comparing to the \texttt{GHC.Generics} implementation of |size|,
we see two improvements. We need one less typeclass, namelly |GSize|, and, the definition
is mainly combinator-based. Considering that the generated \emph{pattern-functor} representation
of a Haskell datatype will already be in a \emph{sums-of-products}, it is better
if we have functions that exploit this extra information. 

  There are still downsides to this approach. A notable one being the need
to carry constraints arround. In fact, the actual |gsize| that one would
write with \texttt{generics-sop} is:

\begin{myhs}
\begin{code}
gsize :: (Generic a , All2 Size (Code a)) => a -> Int
gsize = sum . hcollapse . hcmap (Proxy :: Proxy Size) (mapIK size) . from
\end{code}
\end{myhs}

  The |All2 Size (Code a)| constraint tells the Haskell compiler that
all of the types serving as atoms for |Code a| are an instance of |Size|.
In our case, |All2 Size (Code (Bin a))| expands to |(Size a , Size (Bin a))|.
The |Size| constraint also has to be passed around with a |Proxy| for the
eliminator of the $n$-ary sum. This is a direct consequence of a \emph{shallow}
encoding: since we only unfold one layer of recursion at a time, we have to 
carry proofs that the recursive arguments can also be translated to
a generic representation. We can get rid of this if we add explicit 
least fixpoints to our universe.

\section{Explicit Fix: Deep and Shallow for free}
\label{sec:explicitfix}

\victor{check out \texttt{Fixplate}}
\victor{Mention how without a |Fix| combinator, it is impossible to have a deep encoding}


\TODO{Talk about how do we get both a deep and a shallow
encoding with only one type variable}
\victor{show generic equality or compos.}

\section{Mutual Recursion}
\label{sec:family}
 
\TODO{|El| is \textbf{the} trick, everything else follows}

\section{Template Haskell}
\label{sec:templatehaskell}

\victor{Driving in Auto from Gameplan}

\section{Conclusion}

the usual stuff...