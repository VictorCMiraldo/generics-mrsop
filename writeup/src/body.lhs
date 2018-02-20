\section{Background}
\label{sec:genericprog}

  Before diving head first into our generic programming framework,
lets take a tour on the existing generic programming libraries. We
will be defining a generic |size| function in a couple different variants,
illustrating how different techniques relate and the nuances between them.
This will let us gradually build up to our framework, that borrows the good
ideas from the different approaches and combines them without losing anything.


\victor{I feel that we should mention \texttt{scrap your boilerplate} somehow,
we are almost talking about all of them, right? Regardless, we have a good
argument against them: they require 'Data' and 'Typeable', hence restrict
which external datatypes one can use}

\section{Pattern functors}

  Since version $7.2$, GHC supports some basic, off the shelf, generic
programming using \texttt{GHC.Generics}~\cite{Magalhaes2010}, 
which exposes the \emph{pattern functor} of a datatype. This
allows one to define a function for \emph{any} datatype by induction
on the structure of its representation using \emph{pattern functors}.

  These \emph{pattern functors} are parametrized versions of tuples,
sum-types (|Either|), and unit, empty and constant functors. These provide
a unified view over data: the generic \emph{representation} of values.
The values of a suitable type |a| are translated to this representation
by the means of the |from :: a -> RepGen a| function. We will be using
subscripts to distinguish different representations.

Defining a generic |size| function that provides a measure for any 
value of a supported datatype, for instance, is done in two
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
it can use the generic size function instead of requiring the user
to write her own function. The |gsize| function, on the
other hand, operates on the representation of a datatype
That is our second piece we need to define. We will
do so by another class and will use the instance mechanism to encode
a definition by induction on the structure of the language of representations.
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
we might have an arbitrary type in a position, modelled by the
constant functor. We must require an instance of |Size|
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

  Were we a compiler, we would hapilly issue a \texttt{"No instance
for (Size Int)"} error message at this point. Nevertheless, the
literals of type |Int| illustrate what we call \emph{opaque types}:
those types that constitute the base of the universe and are
\emph{opaque} to the representation language.

  One interesting aspect we should note here is the clearly
\emph{shallow} encoding that |from| provides. That is, we only
represent \emph{one layer} of recursion at a time. For example, in
$(\dagger)$, after unwrapping the calculation of the first
\emph{layer}, we are back to having to calculate |size| for |Bin Int|,
not their representation.

\victor[victor:codes]{In \texttt{GHC.Generics}, the representation has NO CODE;
in fact, that's why we need instance search to perform induction on it.}

  Upon reflecting on the generic |size| function we shown, one can see
a number of issues. Most notably is the amount of boilerplate to
achieve a conceptually simple task: sum up all the sizes of the fields
of whichever constructors make up the value. This is a direct
consequence of not having access to the \emph{sum-of-products}
structure that Haskell's |data| declarations follow. We will see a
different approach, tackling that issue, in
Section~\ref{sec:explicitsop}.  A second issue is the fact that the
generic representation does not carry any information about the
recursive structure of the type.  Instead, we are relying on the
instance search mechanism to figure out that the recursive arguments
can be consumed with the |default size| function. The
\texttt{regular}~\cite{Noort2008} addresses this issue by having a
specific \emph{pattern functor} for recursive positions.


\victor{Should we show how this is 'unsafe' by not having codes.
|Maybe :*: K1 R Int| is a pattern functor; instance search will blow up though;
or just mentioning is enough?}
  Perhaps even more subtle, but also more worrying, is that we have no
guarantees that the |RepGen a| of a type |a| will be defined using
only the supported \emph{pattern functors}. Fixing this would require
one to pin down the language that the representations follow, that is,
the \emph{code} of the datatype, whose semantics give rise to the
\emph{representation} of values. Besides correctnes issues, the
absence \emph{codes} greatly limits the number of generic combinators
one can define. Every generic function has to follow the
\emph{mutually recursive classes} technique we shown.

\victor{this remark seems unnecessary; why would we write the paper if
we don't fix things?}
Later on, in Section~\ref{sec:explicitfix}, we 
show how to successfuly solve both issues.

\subsection{Explicit Sums of Products}
\label{sec:explicitsop}

  Had we had access to a representation of the \emph{sum-of-products}
structure of |Bin|, we could have defined our |gsize| function as we
described it before: sum up the sizes of the fields inside a value,
ignoring the constructor. In fact, the
\texttt{generics-sop}~\cite{deVries2014} library allows one to do
Unlike \texttt{GHC.Generics}, the representation of values is
defined by induction on the \emph{code} of a datatype, this \emph{code}
is a type-level list of lists of |*|, whose semantics is
consonant to a formula in disjunctive normal form.  The outer list is
interpreted as a sum and the each of the inner lists as products.
This section provides an overview of \texttt{generic-sop} as required
to understand our techniques, we refer the reader to the original
paper~\cite{deVries2014} for a more comprehensive explanation.

This extra portion of information allows for a plethora of combinators
to be written. It ultimately allows one to write, with a pinch of
sugar, the |gsize| function as:

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a) => a -> Int
gsize  = sum . elim (map size) . fromSOP
\end{code}
\end{myhs}

  Ignoring the details of the improved |gsize| for a moment, let us focus
on the high level structure. Remembering that |from| now
returns a \emph{sum-of-products} view over the data,
we are using an eliminator, |elim|, do apply a function to the fields
of whatever constructor makes up the value. This eliminator then applies
|map size| to the fields of the constructor, returning something akin
to a |[Int]|. We just need to |sum| them up to obtain the final
size.

  As we hinted earlier, the generic codes consists in 
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

  Back when we were using \emph{pattern functors}, these could be
assembled in any order, we did not even have guarantee that the
arguments to \emph{pattern functors} were themselves \emph{pattern
functors} again! And this is what made the handling of the generic
representations tedious. Now, each datatype has a \emph{code},
|CodeSOP|, which is then interpreted giving rise to the
\emph{representation} of the values fo the datatype in question. T he
key insight here is that we can write combinators that work for
\emph{any} \emph{representation} by induction on the |CodeSOP|, and
this does not require instance search.

  Expectedly, the very \emph{representation}, defined by induction on
|CodeSOP| by the means of $n$-ary sums, |NS|, and $n$-ary products,
|NP|.  These are parametrized by a functor to allow us to use them as
building blocks. 
  Overlooking a slight abuse of notation, one can look at |NS| and |NP|
through the lens of the following isomorphisms:

\begin{align*}
  | NS f [k_1 , k_2 , dots]| &\equiv |f k_1 :+: (f k_2 :+: dots)| \\
  | NP f [k_1 , k_2 , dots]| &\equiv |f k_1 :*: (f k_2 :*: dots)| 
\end{align*}

  We could then define the representation |RepSOP| to be
|NS (NP (K1 R))|, echoing the isomoprihms above, where |data K1 R a = K1 a| 
is being borrowed from \texttt{GHC.Generics}. 
This would then be exactly the representation we get
from \texttt{GHC.Generics}.

\begin{align*}
  |RepSOP (Bin a)|
  &\equiv | NS (NP (K1 R)) (CodeSOP (Bin a))| \\
  &\equiv |K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))| \\
  &\equiv |RepGen (Bin a)|
\end{align*}

  It makes no sense to go through all the trouble of adding the
explicit \emph{sums-of-products} structure to simply forget this
information in the representation, however. Indeed, instead of
piggybacking on \emph{pattern functors}, we define |NS| and |NP| from
scratch using \emph{GADTs}~\cite{Xi2003}, whom play a central role
here.  By pattern matching on the values of |NS| and |NP| we are
informing the typechecker of the structure of the |CodeSOP|.

  An $n$-ary sum |NS f [k_1 , k_2 , dots]|, isomorphic to |Either (f
k_1) (Either (f k_2) dots)|, and an $n$-ary product |NP f [k_1 , k_2 ,
dots]|, isomorphic to |(f k_1 , f k_2 , dots)|, are defined as
follows:

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

  Evidentiating the claim that one can define general combinators for
working with these representations, let us look at a couple of those
combinators. In particular, lets wrte the |elim| and |map| that were
used for the |gsize| function in the beginning of the section.

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
elim :: (forall k dot f k -> a) -> NS f ks -> a
elim f (Here   x)  = f x
elim f (There  x)  = elim f x
\end{code}
\end{myhs}
\end{minipage}\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
map :: (forall k dot f k -> a) -> NP f ks -> [a]
map f  NP0        = []
map f  (x :* xs)  = f x : map f xs
\end{code}
\end{myhs}
\end{minipage}

  Comparing to the \texttt{GHC.Generics} implementation of |size|, we
see two improvements: (A) we need one less typeclass, namelly |GSize|,
and, (B) the definition is combinator-based. Considering that the
generated \emph{pattern functor} representation of a Haskell datatype
will already be in a \emph{sums-of-products}, we do not lose anything
by enforcing this structure.

  There are still downsides to this approach. A notable one being the need
to carry constraints arround. The actual |gsize| one would
write with \texttt{generics-sop} library, adding no sugar, looks like:

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
a generic representation. We can relief this burden by recording,
explicitely, which fields of a constructor are recursive or not.

\section{Explicit Fix: Deep and Shallow for free}
\label{sec:explicitfix}

  Introducing information about the recursive positions in a type is
done by changing the type of atoms in the universe. In
Section~\ref{sec:explicitsop} we had |CodeFix :: * -> (P [ (P [*])])|,
that is, the atoms of the universe were Haskell types. If instead we
create a new kind |Atom|, we can record wether or not a constructor
field is a recursive position or an opaque type.

\begin{myhs}
\begin{code}
data Atom = I | KInt | dots

type family CodeFix (a :: *) :: P [ P [Atom] ]

type instance CodeFix (Bin Int) = P [ P [KInt] , P [I , I] ]
\end{code}
\end{myhs}

  Where |I| is used to mark the recursive positions and |KInt, dots|
are codes for a pretermined selection of Haskell primitive types.
Favoring the simplicity of the presentation, we will stick with only
hardcoded |Int| as the only opaque type in the universe. It is simple
to parametrize the whole development to whatever the user requires, as
we have done in the actual implementation.
\victor{add note that we'll give a link to the repo once review is done}

  The most notable difference is that our code now is not polymorphic.
Back in Section~\ref{sec:explicitsop} we have defined |CodeSOP (Bin
a)|, and this would work for any |a|. This might seen like a
disadvantage, but it is in fact quite the opposite. This allows us to
provide a deep conversion for free, given a shallow conversion. Beyond
doubt one needs to have access to the |CodeSOP a| when converting a
|Bin a| to its (deep) representation. By specifying the types involved
beforehand, we are able to get by without having to carry all of the
constraints we needed in Section~\ref{sec:explicitsop}. We can benefit
the most from this in the simplicity of combinators we are able to write.

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

  Wrapping our |to| and |from| isomorphism into a typeclass and writing the
instance that witnesses that |Bin Int| has a |CodeFix| and is isomorphic
to its representation is quite straight worward.

\begin{myhs}
\begin{code}
class GenericFix a where
  from  :: a -> RepFix a a
  to    :: RepFix a a -> a
\end{code}
\end{myhs}

\begin{myhs}
\begin{code}
type instance CodeFix (Bin Int) = P [ P [KInt] , P [I , I] ]
instance Generic (Bin Int) where
  from (Leaf x)   = Rep (        Here  (NA_K x  :* NP0))
  from (Bin l r)  = Rep (There ( Here  (NA_I l  :* NA_I r :* NP0)))
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

  So far, we are handling the same class of types
as \texttt{regular}~\cite{Noort2008}, but we are imposing 
the representation to follow a \emph{sum-of-products} structure
by the means of |CodeFix|. Those types are guaranteed to have
initial algebra, and indeed, the generic fold is defined
as expected: 

\begin{myhs}
\begin{code}
fold :: (RepFix a b -> b) -> Fix (RepFix a) -> b
fold f = f . fmap (fold f) . unFix
\end{code}
\end{myhs}

  With a solid representation that not only is guaranteed to follow a 
\emph{sum-of-products} structure but also has specific information about
the recursive positions of a type, it is trivial to define even the most
expressive combinators. One such example is the |compos| function, which 
applies a function |f| everywhere on the recursive structure.

\begin{myhs}
\begin{code}
compos :: (Generic a) => (a -> a) -> a -> a
compos f = to . fmap f . from
\end{code}
\end{myhs}

  Although more interesting in the mutually recursive setting,
Section~\ref{sec:family}, we can illustrate its use for traversing a
tree and adding one to its leaves. In fact, a very convoluted way of
writing |fmap (+1) :: Bin Int -> Bin Int| could be:

\begin{myhs}
\begin{code}
example :: Bin Int -> Bin Int
example (Leaf n)  = Leaf (n + 1)
example x         = compos example x
\end{code}
\end{myhs}

  It is worth nothing the \emph{catch-all} case, allowing one to
focus only on the interesting patterns and getting the traversal
of the rest of the datatype for free.
  
  Sometimes we actually want to consume a |Bin Tree| and produce
a single value, but does not need the full expressivity of |fold|. 
Instead, if we know how to consume the opaque types and combine
those results, we can consume any |GenericFix| type.

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

  Finally, we can revisit our running |gsize| example. With the current setting
one can write the simplest generic size function so far:

\begin{myhs}
\begin{code}
gsize :: (Generic a) => a -> Int
gsize = crush (const 1) sum
\end{code}
\end{myhs}

  The deep encoding of |a| allows us to drop the complicated constraints needed
for handling the types of the fields of the constructors of |a|. The information
about the recursive position allows us to write neat combinators like |crush|.
The only thing keeping us from handling real life applications is the limited
form of recursion. When a user requires a generic programming
library, chances are they need to traverse and consume mutually recursive
structures.

\section{Mutual Recursion}
\label{sec:family}

\victor[victor:draft]{Begin draft:}

Mutual recursion means we have many type variables.

We could have made:

\begin{myhs}
\begin{code}
data Atom n 
  = I (Fin n)
  | KInt
  | dots
\end{code}
\end{myhs}

But that is complicated, requires \texttt{-XTypeInType}, and can be 
bypassed: We don't care about malformed codes, as long as they
are \emph{uninhabitable}. Hence:


\begin{myhs}
\begin{code}
data Atom
  = I Nat
  | KInt
  | dots
\end{code}
\end{myhs}

Where |NA| receives a functor that maps a natural number |n|
to the $n$-th type in the mutually recursive family:

\begin{myhs}
\begin{code}
data NA :: (Nat -> *) -> Atom -> * where
  NA_I :: phi n -> NA phi (I n)
  NA_K :: Int   -> NA phi KInt
\end{code}
\end{myhs}

The family can be encoded as a list of types, and a type-level
lookup lets us index them:

\begin{myhs}
\begin{code}
type family Lkup (ls :: [k]) (n :: Nat) :: k where
  Lkup (P [])        _          = TypeError "Gotch'ya! Uninhabitalbe"
  Lkup (x (P :) xs)  (P Z)      = x
  Lkup (x (P :) xs)  ((P S) n)  = Lkup xs n
\end{code}
\end{myhs}

Unfortunately, we can't have |NA (Lkup fam)| because type-families
have to be fully saturated. Solution:

\begin{myhs}
\begin{code}
data El :: [*] -> Nat -> * where
  El :: Lkup fam ix -> El fam ix
\end{code}
\end{myhs}

And that's quite a subtle hack! Now we can have
|type Rep fam a = NS (NP (NA (El fam))) (Code a)| And note that
if |Code a| references any variable with index larger than
|length fam|, then |Rep fam a| is uninhabitable.

Now we tell the reader about our |Family| class and
show a rose tree example.

Then we can show how pretty things become when we add our smart
constructor |into|. 

\subsection{Some cool combinators}

Talk |zipRep|, talk |compos|

\subsection{Parametrized Opaque Types}

Talk about adding a kind |kon| and making everything
receive a |kon -> *| parameter, like in the actual implementation.

\victor{End draft \ref{victor:draft}}

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