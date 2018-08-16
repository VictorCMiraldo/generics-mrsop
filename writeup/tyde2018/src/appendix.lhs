\appendix

\section{The Generic Zipper}
\label{sec:zipper}

  To add to our examples section we conduct a validation
exercise involving a more complex application of generic
programming. Zippers~\cite{Huet1997} are a well established technique
for traversing a recursive data structure keeping track of the current
\emph{focus point}. Defining generic zippers is nothing new, this has
been done by many authors~\cite{Hinze2004,Adams2010,Yakushev2009} for
many different classes of types in the past. To the best of the
authors knowledge, this is the first definition in a direct
\emph{sums-of-products} style.  We will not be explaining 
\emph{are} zippers are in detail, instead, we will give a quick reminder
and show how zippers fit within our framework.

  Generally speaking, the zipper keeps track of a focus point in a
data structure and allows for the user to conveniently move this focus
point and to apply functions to whatever is under focus.  This focus
point is expressed by the means of a location type, |Loc|, with a
couple of associated functions:

\begin{myhs}
\begin{code}
up , dowm , right  :: Loc a -> Maybe (Loc a)
update             :: (a -> a) -> Loc a -> Loc a
\end{code}
\end{myhs}

  Where |a| and |Loc a| are isomorphic, and can be converted by the
means of |enter| and |leave| functions. For instance, the composition
of |down|, |down|, |right| , |update f| will essentially move the
focus two layers down from the root, then one element to the right and
apply function |f| to the focused element, as shown below.

\begin{center}
\begin{tabular}{m{.2\linewidth} m{.15\linewidth} m{.2\linewidth}}
\begin{forest}
  [|a|,draw [|b| [|c_1|] [|c_2|] [|c_3|]] [|d|]]
\end{forest}
  & { \qquad \centering $\Rightarrow$ } &
\begin{forest}
  [|a| [|b| [|c_1|] [|f c_2|,draw] [|c_3|]] [|d|]]
\end{forest}
\end{tabular}
\end{center}

  In our case, this location type consists of a distinguished element
of the family |El fam ix| and a stack of contexts with a hole of type |ix|, where
we can plug in the distinguished element. This stack of contexts may build
a value whose type is a different member of the family; we recall its index
as |iy|. 

For the sake of conciseness we present the datatypes for a fixed interpretation
of opaque types |ki :: kon -> Star|, a family |fam ::
[Star]| and its associated codes |codes :: [[[Atom kon]]]|.
In the actual implementation all those elements appear as additional
parameters to |Loc| and |Ctxs|.

\begin{myhs}
\begin{code}
data Loc :: Nat -> Star where
  Loc :: El fam iy -> Ctxs ix iy -> Loc ix
\end{code}
\end{myhs}

  The second field of |Loc|, the stack of contexts,
represents how deep into the recursive
tree we have descended so far. Each time we unwrap another layer of recursion,
we push some context onto the stack to be able to go back up. Note how
the |Cons| constructor resembles some sort of composition operation.

\begin{myhs}
\begin{code}
data Ctxs :: Nat -> Nat -> Star where
  Nil   :: Ctxs ix ix
  Cons  :: Ctx (Lkup codes iz) iy -> Ctxs ix iz -> Ctxs ix iy
\end{code}
\end{myhs}

  Each element in this stack is an individual context, |Ctx c iy|.
A context is defined by a choice of a constructor
for the code |c|, paired a product of the correct type where one 
of the elements is a hole. This hole represents where the distinguished element
in |Loc| was supposed to be. 

\begin{myhs}
\begin{code}
data Ctx :: [[Atom kon]] -> Nat -> Star where
  Ctx :: Constr n c -> NPHole (Lkup n c) iy -> Ctx c iy

data NPHole :: [Atom kon] -> Nat -> Star where
  Here   :: NP (NA ki (El fam)) xs            -> NPHole (I ix  : xs)  ix
  There  :: NA ki (El fam) x -> NPHole xs ix  -> NPHole (x     : xs)  ix
\end{code}
\end{myhs}

  The navigation functions are a direct translation of those defined 
for the \texttt{multirec}~\cite{Yakushev2009} library, that use the
|first|, |fill|, and |next| primitives for working over |Ctx|s.
The |fill| function can be taken over almost unchanged, whereas |first| and |next| require
a simple trick: we have to wrap the |Nat| parameter of |NPHole| in an
existential in order to manipulate it conveniently. The |ix| is packed up in an existential
type since we do not really know beforehand which member of the mutually
recursive family is seen first in an arbitrary product.

\begin{myhs}
\begin{code}
data NPHoleE :: [Atom kon] -> Star where
  Witness :: El fam ix -> NPHole c ix -> NPHoleE c
\end{code}
\end{myhs}

  Now we can define the |firstE| and |nextE|, the counterparts of
|first| and |next| from \texttt{multirec}. Intuitively,
|firstE| returns the |NPHole| with the 
first recursive position (if any) selected, |nextE| tries to find the
next recursive position in an |NPHole|. These functions have the following types:

\begin{myhs}
\begin{code}
firstE  :: NP (NA ki (El fam)) xs  -> Maybe (NPHoleE xs)
nextE   :: NPHoleE xs              -> Maybe (NPHoleE xs)
\end{code}
\end{myhs}

  To conclude we can now use flipped compositions for pure functions 
|(>>>) :: (a -> b) -> (b -> c) -> a -> c| and monadic functions
|(>=>) :: (Monad m) => (a -> m b) -> (b -> m c) -> a -> m c| to elegantly
write some \emph{location based} instruction to transform some value
of the type |LambdaTerm| defined in \Cref{sec:alphaequivalence}.
Here |enter| and |leave| witness the isomorphism between |El fam ix|
and |Loc ix|.

\begin{myhs}
\begin{code}
tr :: LambdaTerm -> Maybe LambdaTerm
tr = enter  >>>  down 
            >=>  right 
            >=>  update (const $ Var "c") 
            >>>  leave 
            >>>  return


tr (App (Var "a") (Var "b")) 
  == Just (App (Var "a") (Var "c"))
\end{code} %$
\end{myhs}

  We invite the reader to check the source code for a more detailed
account of the generic zipper.
In fact, we were able to provide the same zipper interface 
as the \texttt{multirec} library. Our implementation is shorter, however.
This is because we do not need type classes to implement |firstE| and |nextE|.


\section{Template Haskell}
\label{sec:templatehaskell}

  Having a convenient and robust way to get the |Family| instance for
a given selection of datatypes is paramount for the usability of our
library. In a real scenario, a mutually recursive family
may consist of many datatypes with dozens of
constructors. Sometimes these datatypes are written with parameters,
or come from external libraries.

Our goal is to automate the generation of |Family| instances under all
those circumstances using \emph{Template Haskell}~\cite{Sheard2002}.
From the programmers' point of view, they only need to call |deriveFamily|
with the topmost (that is, the first) type of the family. For example:

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

  The |deriveFamily| takes care of unfolding the (type level) recursion until it
reaches a fixpoint.  In this case, the type synonym |FamProgString = P [Prog
String , dots]| will be generated, together with its |Family|
instance. Optionally, one can also pass along a custom function to decide
whether a type should be considered opaque. By default, it uses a
selection of Haskell built-in types as opaque types.

\subsection{Unfolding the Family}
\label{sec:underthehood}

  The process of deriving a whole mutually recursive family from a single
member is conceptually divided into two disjoint processes. First we unfold all definitions
and follow all the recursive paths until we reach a fixpoint. At that moment
we know that we
have discovered all the types in the family. Second, we translate the definition
of those types to the format our library expects.
During the unfolding process we keep a key-value map in a 
|State| monad, keeping track of the types we have seen, the types we have
seen \emph{and} processed and the indices of those within the family.

  Let us illustrate this process in a bit more detail using our running example
of a
mutually recursive family and consider what
happens within \emph{Template Haskell} when it starts unfolding 
the |deriveFamily| clause.

\begin{myhs}
\begin{code}
data Rose a  = Fork a [Rose a]
data [a]     = nil | a : [a]

deriveFamily (tht (Rose Int))
\end{code}
\end{myhs}

  The first thing that happens is registering that we seen the type |Rose Int|.
Since it is the first type to be discovered, it is assigned index zero
within the family.
Next we need to reify the definition of |Rose|. At this point,
we query \emph{Template Haskell} for the definition, and we obtain
|data Rose x = Fork x [Rose x]|. Since |Rose| has kind |Star -> Star|, it cannot
be directly translated -- our library only supports ground types, which
are those with kind |Star|.
But we do not need a generic definition for |Rose|, we just need the specific case where |x = Int|.
Essentially, we just apply the reified definition of |Rose| to |Int| and $\beta$-reduce it,
giving us |Fork Int [Rose Int]|.

The next processing step is looking into
the types of the fields of the (single) constructor |Fork|. First we see |Int| and
decide it is an opaque type, say |KInt|. Second, we see |[Rose Int]| and
notice it is the first time we see this type. Hence, we register it with a fresh
index, |S Z| in this case. The final result for |Rose Int| is |P [P [K KInt, I (S Z)]]|.

We now go into |[Rose Int]| for processing.
Once again we need to perform some amount of $\beta$-reduction
at the type level before inspecting its fields.
The rest of the process is the same that for |Rose Int|.
However, when we encounter the field of type |Rose Int| this is already
registered, so we just need to use the index |Z| in that position.

  The final step is generating the actual Haskell code from the data obtained
in the previous process. This is a very
verbose and mechanical process, whose details we
omit. In short, we generate the necessary type synonyms, pattern synonyms,
the |Family| instance, and metadata information.  The generated type
synonyms are named after the topmost type of the family, passed to
|deriveFamily|:

\begin{myhs}
\begin{code}
type  FamRoseInt
      = P [ Rose Int                    , [Rose Int] ]
type  CodesRoseInt
      = P [ (P [P [K KInt , I (S Z)]])  , P [ P [] , P [I Z , I (S Z) ] ] ]
\end{code}
\end{myhs}

  Pattern synonyms are useful for convenient pattern matching and injecting into
the |View| datatype. We produce two different kinds of pattern synonyms.
First, synonyms for generic representations, one per constructor. Second,
synonyms which associate each type in the recursive family with their
position in the list of codes.

\vspace{.1cm}
\begin{myhs}
%format forkP = "\HT{\overline{Fork}}" 
%format nilP  = "\HT{\overbar{[]}}" 
%format consP = "\HT{\overline{:}}" 
\begin{code}
pattern forkP x xs  = Tag SZ       (NA_K x :* NA_I xs :* NP0)
pattern nilP        = Tag SZ       NP0
pattern x consP xs  = Tag (SS SZ)  (NA_I x :* NA_I xs :* NP0)

pattern (Pat RoseInt)      = SZ
pattern (Pat ListRoseInt)  = SS SZ
\end{code}
\end{myhs}

\vspace{.2cm}
  The actual |Family| instance is exactly as the one shown in \Cref{sec:family}

\begin{myhs}
\begin{code}
instance Family Singl FamRoseInt CodesRoseInt where dots
\end{code}
\end{myhs}


\section{Metadata}
\label{sec:metadata}

  The representations described in this paper is enough to write generic equalities
and zippers. But there is one missing ingredient to derive generic
pretty-printing or conversion to JSON, for instance. We need to maintain
the \emph{metadata} information of our datatypes.
This metadata includes the datatype name, the module where it was defined,
and the name of the constructors. Without this
information you cannot write a function which outputs the string
\begin{verbatim}
Fork 1 [Fork 2 [], Fork 3 []]
\end{verbatim}
for a call to |genericShow (Fork 1 [Fork 2 [], Fork 3 []])|. The reason is that
the code of |Rose Int| does not contain the information that the constructor
of |Rose| is called |"Fork"|.

  Like in \texttt{generics-sop}~\cite{deVries2014}, having the code
for a family of datatypes available allows for a completely separate
treatment of metadata. This is yet another advantage of the
sum-of-products approach when compared to the more traditional pattern
functors. In fact, our handling of metadata is heavily inspired from
\texttt{generics-sop}, so much so that we will start by explaining a simplified version of
their handling of metadata, and then outline the differences to our approach. 

  The general idea is to store the meta information following the structure of
the datatype itself. So, instead of data, we keep track of the names of the
different parts and other meta information that can be useful. It is advantageous
to keep metadata separate from the generic representation as it would only
clutter the definition of generic functionality.
This information is tied to a datatype by means of an additional type class
|HasDatatypeInfo|.
Generic functions may now query the metadata by means of functions like
|datatypeName|, which reflect the type information into the term level.
The definitions are given in \Cref{fig:sopmeta}.

\begin{figure*}
\begin{myhs}
\begin{code}
data DatatypeInfo :: [[Star]] -> Star where
  ADT  :: ModuleName -> DatatypeName -> NP  ConstructorInfo cs       -> DatatypeInfo cs
  New  :: ModuleName -> DatatypeName ->     ConstructorInfo (P [c])  -> DatatypeInfo (P [ P [ c ]])

data ConstructorInfo :: [Star] -> Star where
  Constructor  :: ConstructorName                             -> ConstructorInfo xs
  Infix        :: ConstructorName -> Associativity -> Fixity  -> ConstructorInfo (P [ x, y ])
  Record       :: ConstructorName -> NP FieldInfo xs          -> ConstructorInfo xs

data FieldInfo :: Star -> Star where
  FieldInfo :: FieldName -> FieldInfo a

class HasDatatypeInfo a where
  datatypeInfo :: proxy a -> DatatypeInfo (Code a)
\end{code}
\end{myhs}
\caption{Definitions related to metadata from \texttt{generics-sop}}
\label{fig:sopmeta}
\end{figure*}


Our library uses the same approach to handle metadata. In fact, the code remains
almost unchanged, except for adapting it to the larger universe of
datatypes we can now handle. Unlike \texttt{generic-sop}, our list of lists
representing the sum-of-products structure does not contain types of kind |Star|,
but |Atom|s. All the types representing metadata at the type level must be
updated to reflect this new scenario:
\begin{myhs}
\begin{code}
data DatatypeInfo     :: [  [  Atom kon ]]  -> Star where ...
data ConstructorInfo  ::    [  Atom kon ]   -> Star where ...
data FieldInfo        ::       Atom kon     -> Star where ...
\end{code}
\end{myhs}

As we have discussed above, our library is able to generate codes not only
for single types of kind |Star|, like |Int| or |Bool|, but also for types which
are the result of type level applications, such as |Rose Int| and |[Rose Int]|.
The shape of the metadata information in |DatatypeInfo|, a module name plus
a datatype name, is not enough to handle these cases. 
We replace the uses of |ModuleName| and |DatatypeName| in 
|DatatypeInfo| by a richer promoted type |TypeName|, which can
describe applications, as required.
\begin{myhs}
\begin{code}
data TypeName  =  ConT ModuleName DatatypeName
               |  TypeName :@: TypeName

data DatatypeInfo :: [[Atom kon]] -> Star where
  ADT  ::  TypeName  -> NP  ConstructorInfo cs
       ->  DatatypeInfo cs
  New  ::  TypeName  ->     ConstructorInfo (P [c])
       ->  DatatypeInfo (P [ P [ c ]])
\end{code}
\end{myhs}

The most important difference to \texttt{generics-sop}, perhaps, 
is that the metadata is not defined for a single type, but
for a type \emph{within} a family. This is reflected in the new signature of 
|datatypeInfo|, which receives proxies for both the family and the type.
The type equalities in that signature reflect the fact that the given type
|ty| is included with index |ix| within the family |fam|. This step is needed
to look up the code for the type in the right position of |codes|.
\begin{myhs}
\begin{code}
class (Family kappa fam codes)
       =>  HasDatatypeInfo kappa fam codes ix 
       |   fam -> kappa codes where
  datatypeInfo  ::  (ix ~ Idx ty fam , Lkup ix fam ~ ty)
                =>  Proxy fam -> Proxy ty
                ->  DatatypeInfo (Lkup ix codes)
\end{code}
\end{myhs}

  The Template Haskell will then generate something similar to
the instance below for the first type in the family, |Rose Int|:

\begin{myhs}
\begin{code}
instance HasDatatypeInfo Singl FamRose CodesRose Z where
  datatypeInfo _ _ 
    =  ADT (ConT "E" "Rose" :@: ConT "Prelude" "Int")
    $  (Constructor "Fork") :* NP0
\end{code} %$
\end{myhs}

Once all the metadata is in place, we can use it in the same fashion
as \texttt{generics-sop}. We refer the interested reader to
\citet{deVries2014} for examples.
