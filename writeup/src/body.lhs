\section{Background}
\label{sec:genericprog}

\alejandro{We need a small paragraph here}

\section{Pattern functors}

\victor[victor:codes]{In \texttt{GHC.Generics}, the representation has NO CODE;
in fact, that's why we need instance search to perform induction on it.
I need to mention this somehow }


  Since version $7.2$, GHC supports some basic, off the shelf, generic
programming using \texttt{GHC.Generics}~\cite{Magalhaes2010}, 
which exposes the \emph{pattern functor} of a datatype. This
allows one to define a function for \emph{any} datatype by induction
on the structure of its representation using \emph{pattern functors}.

\victor{Do I have to explain pattern-functors here?}
\alejandro{Explain that you are using subscript |gen| to distinguish this
|Gen| from those of other libraries}

Defining a generic |size| function that provides a measure of the 
value in question, for instance, is done in two
steps. First, we define a class that exposes a |size| function
for values in kind |*|:

\begin{myhs}
\begin{code}
class Size (a :: *) where
  size :: a -> Int
  default size  :: (Generic a , GSize (RepGen a))
                => a -> Int
  size = gsize . fromGen
\end{code}
\end{myhs}

  The default keyword instructs Haskell to use the provided
implementation whenever the constraint |(GenericGen a , GSize (RepGen a))| 
can be satisfied when declaring an instance for |Size a|.
In a nutshell, we are saying that if Haskell
is aware of a generic representation for values of type |a|,
it can use the generic size function. The |gsize| function, on the
other hand, operates on the representation of a datatype
That is our second piece we need to define. We will
do so by another class and will use the instance mechanism to encode
induction on the structure of the language of representations.
Here, they are \emph{pattern functors}.

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

  We still have to handle the cases were 
we might have an arbitrary type in a position. 
We must, then, require this type to be an instance of |Size|
so we can sucessfully tie the recursive knot.

\begin{myhs}
\begin{code}
instance (Size a) => GSize (K1 R a) where
  gsize (K1 a) = size a
\end{code}
\end{myhs}

  This technique of \emph{mutually recursive classes} is quite 
specific to \texttt{GHC.Generics} flavor of generic programming.
It is worthwhile to illustrate how the compiler would go about choosing
instances for computing |size (Bin (Leaf 1) (Leaf 2))|:

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
we call \emph{opaque types}: those types that constitute the base of the universe
and are \emph{opaque} to the representation language.

  One interesting aspect we should note here is the clearly \emph{shallow} encoding
that |from| provides. That is, we only represent \emph{one layer} of recursion
at a time. For example, in $(\dagger)$, after unwrapping the calculation of the first
\emph{layer}, we are back to having to calculate |size| for |Bin Int|, not their 
representation.

  Upon reflecting on the generic |size| function we shown, one can 
see a number of issues. Most notably is the amount of boilerplate to achieve a 
conceptually simple task: sum up all the sizes of the fields of whichever constructors 
make up the value. This is a direct consequence of not having access to 
the \emph{sum-of-products} structure that Haskell's |data| declarations follow. 
We will see a different approach, tackling that issue, in Section~\ref{sec:explicitsop}. 
A second issue is the fact that the generic representation 
does not carry any information about the recursive structure of the type.
Instead, we are relying on the instance search
mechanism to figure out that the recursive arguments can be treated
with the default |size| function. The immediate consequence the very limited
number of combinators one can define. Every generic functrion has to
follow the \emph{mutually recursive classes} technique we shown. The 
\texttt{regular}~\cite{Noort2008} addresses this later issue, but not the former. 
Later on, in Section~\ref{sec:explicitfix}, we show how to successfuly 
solve both issues.

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
allows one to do precisely that. The language of representations is
different from \texttt{GHC.Generics}. Instead of using binary \emph{pattern-functors},
we will use list of lists, whose semantics is consonant to a formula in disjunctive normal form.
The outer list is interpreted as an $n$-ary sum and the inner lists as $n$-ary products.
This section provides an overview of \texttt{generic-sop} as required to
understand our techniques, we refer the reader to the original paper~\cite{deVries2014} for a
more comprehensive explanation.

\alejandro{Maybe just ``sums'' and ``products'' instead of $n$-ary. The fact
that the same $n$ is used for both make it look like they have to coincide.}

This extra
portion of information allows for a plethora of combinators to be written.
It ultimately allows one to write, with a pinch of sugar, the |gsize| function as:

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a) => a -> Int
gsize  = sum . elim (map size) . fromSOP
\end{code}
\end{myhs}

  Ignoring the details of the new |gsize| for a moment, let us focus
on the high level structure. Remembering that |from| now
returns a \emph{sum-of-products} view over the data,
we are using an eliminator, |elim|, do apply a function to the fields
of whatever constructor makes up the value. This eliminator then applies
|map size| to the fields of the constructor, returning something akin
to a |[Int]|. We just need to |sum| them up to obtain the final
size.

  As we hinted earlier, the generic representation consists in 
a type-level list of lists. The outer list represents the 
constructors of a type, and will be interpreted as a $n$-ary sum, whereas
the inner lists are interepreted as the fields of the respective constructors,
interpreted as $n$-ary products.

\begin{myhs}
\begin{code}
type family    CodeSOP (a :: *) :: P ([ (P [*]) ])

type instance  CodeSOP (Bin a) = P ([ P [a] , P ([Bin a , Bin a]) ])
\end{code}
\end{myhs}

  Back when we were using \emph{pattern-functors}, these could be assembled in
any order. This was really what made the handling of the generic representations
tedious. Now, each datatype gives rise to a |CodeSOP|, which is then interpreted
giving rise to the \emph{representation} of the data in question. The key insight
here is that we can write combinators that work for the \emph{representation}
of any |Code| by induction on the |CodeSOP|.

  Expectedly, the very \emph{representation} is defined by induction on |CodeSOP|.
The \texttt{generics-sop} then defines a couple \emph{GADTs}~\cite{Xi2003} 
that act as $n$-ary sums, |NS|, and products, |NP|. These are parametrized
by a functor to allow us to use them as building blocks.

  Overlooking a slight abuse of notation, one can say that the following
isomorphisms hold:

\begin{align*}
  | NS f [k_1 , k_2 , dots]| &\equiv |f k_1 :+: (f k_2 :+: dots)| \\
  | NP f [k_1 , k_2 , dots]| &\equiv |f k_1 :*: (f k_2 :*: dots)| 
\end{align*}

  We could then define the representation |RepSOP| to be
defined as |NS (NP (K1 R))|, where |data K1 R a = K1 a| 
is being borrowed from \texttt{GHC.Generics}.
As it is, this would be exactly the representation we get
from \texttt{GHC.Generics}.

\begin{align*}
  |RepSOP (Bin a)|
  &\equiv | NS (NP (K1 R)) (CodeSOP (Bin a))| \\
  &\equiv |K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))| \\
  &\equiv |RepGen (Bin a)|
\end{align*}

  It makes no sense to go through all the trouble of adding the explicit \emph{sums-of-products}
structure to simply forget this information in the representation, however. Indeed,
instead of piggybacking on \emph{pattern-functors}, we define |NS| and |NP|
from scratch.

  An $n$-ary sum |NS f [k_1 , k_2 , dots]|, isomorphic to |Either (f k_1) (Either (f k_2) dots)|, 
and an $n$-ary product |NP f [k_1 , k_2 , dots]|, isomorphic to |(f k_1 , f k_2 , dots)|,
are defined as follows: 

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k (P (:)) ks)
  There  :: NS f ks  -> NS f (k (P (:)) ks)
\end{code}
\end{myhs}
\end{minipage}\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NP :: (k -> *) -> [k] -> * where
  NP0  ::                    NP f (P [])
  :*   :: f x -> NP f xs ->  NP f (x (P (:)) xs)
\end{code}
\end{myhs}
\end{minipage}

  Finally, since our atoms are of kind |*|, we can use the identity
functor, |I|, to interpret those and can finally define the representation
of values of a type |a| under the \emph{SOP} view:

\begin{myhs}
\begin{code}
type RepSOP a = NS (NP I) (CodeSOP a)

newtype I (a :: *) = I { unI :: a }
\end{code}
\end{myhs}

  Revisiting the |gsize| example above, we can illustrate the flavor
of combinators that can be encoded for this approach. The |map| used
in the definition of |gsize| has type |(forall k dot f k -> a) -> NP f ks -> [a]|, 
and can be defined analogously to the the sum eliminator |elim|:

\begin{myhs}
\begin{code}
elim :: (forall k dot f k -> a) -> NS f ks -> a
elim f (Here   x)  = f x
elim f (There  x)  = elim f x
\end{code}
\end{myhs}

  Comparing to the \texttt{GHC.Generics} implementation of |size|,
we see two improvements. We need one less typeclass, namelly |GSize|, and, the definition
is combinator-based. Considering that the generated \emph{pattern-functor} representation
of a Haskell datatype will already be in a \emph{sums-of-products}, 
we do not lose anything by keeping this information around.

  There are still downsides to this approach. A notable one being the need
to carry constraints arround. In fact, the actual |gsize| one would
write with \texttt{generics-sop} without any sugar looks like:

\begin{myhs}
\begin{code}
gsize :: (Generic a , All2 Size (CodeSOP a)) => a -> Int
gsize = sum . hcollapse . hcmap (Proxy :: Proxy Size) (mapIK size) . fromSOP
\end{code}
\end{myhs}

  The |All2 Size (CodeSOP a)| constraint tells the compiler that
all of the types serving as atoms for |CodeSOP a| are an instance of |Size|.
In our case, |All2 Size (CodeSOP (Bin a))| expands to |(Size a , Size (Bin a))|.
The |Size| constraint also has to be passed around with a |Proxy| for the
eliminator of the $n$-ary sum. This is a direct consequence of a \emph{shallow}
encoding: since we only unfold one layer of recursion at a time, we have to 
carry proofs that the recursive arguments can also be translated to
a generic representation. We can relief this burden by adding explicit 
least fixpoints to our universe of representations.

\section{Explicit Fix: Deep and Shallow for free}
\label{sec:explicitfix}

  Introducing information about the recursive positions in a type
is done by changing the type of atoms in the universe. In Section~\ref{sec:explicitsop}
we had |CodeFix :: * -> (P [ (P [*])])|, that is, the atoms of the universe were
Haskell types. If instead we create a new kind |Atom|, we can record wether or not
a constructor field is a recursive position or an opaque type.

\begin{myhs}
\begin{code}
data Atom = I | KInt

type family CodeFix (a :: *) :: P [ P [Atom] ]

type instance CodeFix (Bin Int) = P [ P [KInt] , P [I , I] ]
\end{code}
\end{myhs}

\alejandro{Mention that |I| is how we mark recursive positions.}

  Here we are considering that an |Atom| is either a recursive
position or an opaque type, in this case, an |Int|. Favoring the simplicity of the presentation,
we will stick with a hardcoded |Int| as the only opaque type in the universe. It is simple to
parametrize the whole development to whatever the user requires, as we have done 
in the actual implementation. 

  The most notable difference is that our code now is not polymorphic. 
Back in Section~\ref{sec:explicitsop} we have defined |CodeSOP (Bin a)|, and this
would work for any |a|. This might seen like a disadvantage, but it is in fact 
quite the opposite. This allows us to provide a deep conversion for free, given
a shallow conversion. Beyond doubt one needs to have access to the |CodeSOP a|
when converting a |Bin a| to its (deep) representation. By specifying the types
involved beforehand, we are able to get by without having to carry all
of the constraints we needed in Section~\ref{sec:explicitsop}.

  The representation of our codes now requires a functor that map |Atom|s into
Haskell values, that is, |Atom -> *|. The representation |RepFix| is remarkably 
similar to |RepSOP|, but since we now know the recursive positions, we are
able to lift the representation to a functor. In fact, it is a nice exercise to
write the |Functor (RepFix a)| instance. We are using a |newtype| here so
we can partially apply |RepFix|.

\begin{myhs}
\begin{code}
data NA :: * -> Atom -> * where
  NA_I :: x    -> NA x I
  NA_K :: Int  -> NA x KInt

newtype RepFix a x = Rep { unRep :: NS (NP (NA x)) (Code a) }
\end{code}
\end{myhs}

  Let us create an interface to unify the vocabulary for types that
can be translated to some generic representation. In fact, we just
need these types to have an associated |Code| and a function to and from
the interpretation of their |Code|. These functions witness an isomorphism.

\begin{myhs}
\begin{code}
class Generic a where
  from  :: a -> RepFix a a
  to    :: RepFix a a -> a
\end{code}
\end{myhs}

  The instance for |Generic (Bin Int)| is quite straight forward, then.

\begin{myhs}
\begin{code}
type instance CodeFix (Bin Int) = P [ P [KInt] , P [I , I] ]
instance Generic (Bin Int) where
  from (Leaf x)   = Rep (Here (NA_K x :* NP0))
  from (Bin l r)  = Rep (There (Here (NA_I l :* NA_I r :* NP0)))
\end{code}
\end{myhs}

  Note how |RepFix| still is a shallow representation. But by
constructing the least fixpoint of |RepFix a| we can obtain the deep
encoding for free, by simply recursively translating each
layer of the shallow encoding.

\begin{myhs}
\begin{code}
newtype Fix f = Fix { unFix :: f (Fix f) }

deepFrom :: (Generic a) -> a -> Fix (RepFix a)
deepFrom = Fix . fmap deepFrom . from
\end{code}
\end{myhs}

  Besides the usual combinators, like |compos|:

\begin{myhs}
\begin{code}
compos :: (Generic a) => (a -> a) -> a -> a
compos f = to . fmap f . from
\end{code}
\end{myhs}

\alejandro{Explain here why |compos| is useful, and mention that other
generic libraries take it as a basis for other functions.}

  we are also able to expoit the \emph{sum-of-products} structure
to write expressive combinators, such as |crush|, that consumes opaque
types and combine the results of the products into a single result.

\begin{myhs}
\begin{code}
crush :: (Generic a) => (forall x dot Atom KInt x -> b) -> ([b] -> b) -> a -> b
crush k cat = crushFix . deepFrom
  where
    crushFix :: Fix (RepFix a) -> b
    crushFix = cat . elimNS (elimNP go) . unFix

    go (NA_I x) = crushFix x
    go (NA_K i) = k i
\end{code}
\end{myhs}

  Finally, we can revisit our |gsize| example and write the simplest |gsize| so far:

\begin{myhs}
\begin{code}
gsize :: (Generic a) => a -> Int
gsize = crush (const 1) sum
\end{code}
\end{myhs}

  \victor{No need for any typeclass; no need for any constraint; simple and straight forward definition}


\victor{check out \texttt{Fixplate}}
\victor{Mention how without a |Fix| combinator, it is impossible to have a deep encoding}


\TODO{Talk about how do we get both a deep and a shallow
encoding with only one type variable}
\victor{show generic equality or compos.}

\section{Mutual Recursion}
\label{sec:family}

\victor{Turns out that chapter 2 of the Multirec paper already mentions this
deep vs shallow drama}
 
\TODO{|El| is \textbf{the} trick, everything else follows}

\section{Template Haskell}
\label{sec:templatehaskell}

\victor{I'm assuming we have already introduced the 
usual RoseTree family: |data Rose a = Fork a [Rose a]|}

\victor{The glue text should mention how boring and mechanical it is to 
have to write the |Family| instance by hand}

  Having a convenient and robust way to get the |Family| instance
for a certain selection of datatypes is paramount for the usability
of the library. The goal is to take mechanical work away from the
programmer, and not introduce more, after all. In a real scenario,
the typical mutually recursive family will be constituted of dozens
of datatypes with tens of dozens of constructors. Sometimes these
datatypes are written with parameters, or come from external libraries.
There are many difficulties to a fully automatic interface to deriving |Family|
instances.

\subsection{The User Interface}
\label{sec:thapi}

  All that the programmer have to do to derive their |Family|
instance is call the \emph{Template Haskell}~\cite{Sheard2002} 
function |deriveFamily| and pass the (fully saturated) type that
is the topmost type in the family:

\newcommand{\shspc}{\hspace{-0.05em}}
%format (tht (a)) = "\HSSym{[\shspc t\shspc|}" a "\HSSym{|\shspc]}"
\begin{myhs}
\begin{code}
data Exp   var = dots
data Stmt  var = dots
data Decl  var = dots
data Prog  var = dots

deriveFamily (tht (Prog String))
\end{code}
\end{myhs}

  \victor{Explain the splicing idea; mention that |Prog String| will
be the |Lkup Z Fam| type}

\subsection{Under the Hood}
\label{sec:underthehood}

  The process of deriving a whole mutually recursive family from a single
member is mainly divided in two disjoint process. First we unfold all definitions
and follow all the recursive paths until we reach a fixpoint and, hence,
have discovered all types in the family. Second, we translate the definition
of the previously discovered types to the format our library expects.

  Let us illustrate this process in a bit more detail using the cannonical
mutually recursive family example and walking through what
happens inside \emph{Template Haskell}~\cite{Sheard2002} when it starts unfolding 
the |deriveFamily| clause.

%format :>: = "\HSCon{\triangleright}"
\begin{myhs}
\begin{code}
data Rose a  = a :>: [Rose a]
data [a]     = nil | a : [a]

deriveFamily (tht (Rose Int))
\end{code}
\end{myhs}

  \victor{I'm using type-level naturals in the following}
  

  The first thing that happens is registering the type |Rose Int| as being 
indexed by |Z|. But we have not yet processed it. We need to reify
the definition of |Rose| and apply it to |Int| in order to get the 
the type of |:>:| that will belong in the family. In fact, after reifying |Rose Int|
and $\beta$-reducing it we get something like 
|(\ a -> a :>: [Rose a]) Int == Int :>: [Rose Int]|. We now have to
process the fields of |Int :>: [Rose Int]|, and once we are done, convert them
to |Atom|s. The first field will be an opaque type |KInt|, but the second
needs further processing, as it is the first time we encounter the type |[Rose Int]|.
Same story as before. Start by registering |[Rose Int]| to a fresh index, in this case |S Z|.
Reify the topmost application and $\beta$-reduce: |(\ a -> nil || a : [a]) (Rose Int) ==| 
|nil || (Rose Int) : [Rose Int]|. We now go over the fields of each constructor
and see what still needs processing. Turns out we are done since there is no
type we have not seen before as both |Rose Int| and |[Rose Int]| have been
registered with indexes |Z| and |S Z| respectively. We can then issue
the codes:


\begin{myhs}
\begin{code}
type CodeRoseInt      = (P [ (P [ KInt , I (S Z) ]) ])
type CodeListRoseInt  = (P [ (P [ ]) , (P [ I Z , I (S Z) ]) ])
\end{code}
\end{myhs}

  \victor{I'm not sure I should delve in more details about
the actual implementation. Does the description suffice?}

  \victor{Should we talk about the generation of pattern synonyms
to help with the manipulation of deeply embedded values?}

\subsection{Temp. Summary}

  \victor{Stress that we have achieved what we were looking for:
\begin{description}
  \item[Convenience:] The user jsut tells the top-most type
    of the family. Changes in the family don't require changes
    in the code (unless they are gigantic changes, obviously).
  \item[Robustness:] Having a type-level reduction mechanism
    allows us to let the user make use of types such as |Maybe|
    or |[ ]| and the mechanism will consider those as members of
    the family.
\end{description}}


  In order to derive a whole mutually recursive family from just one of
the members of the family requires some engineering. 

We have to be able to automatically handle all of these cases for
a satisfying \emph{template haskell} mechanism.

\victor{Driving in Auto from Gameplan}

\section{Conclusion}

the usual stuff...