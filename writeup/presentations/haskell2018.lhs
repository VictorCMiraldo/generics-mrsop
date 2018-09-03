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
  \frametitle{Representing Datatypes (\texttt{generics-sop})}

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

  \pause
  Given a map from |PL (PL Star)| into |Star|, call it |Rep|, package:
\begin{code}
class Generic a where
  from  :: a -> Rep (Code a)
  to    :: Rep (Code a) -> a
\end{code}

\end{frame}


\begin{frame}
  \frametitle{N-ary Sums and Products}

%format x_1 = "\HV{x_1}"
%format x_n = "\HV{x_n}"
\begin{code}
NS p (LIST (x_1 , dots , x_n)) isoto Either (p x_1) (Either dots (p x_n))
NP p (LIST (x_1 , dots , x_n)) isoto (p x_1 , dots , p x_n)
\end{code}
\pause
\begin{code}
data NS :: (k -> Star) -> LISTKS -> Star where
  Here   :: f x      -> NS f (x (P (:)) xs)
  There  :: NS f xs  -> NS f (x (P (:)) xs)
space
data NP :: (k -> Star) -> LISTKS -> Star where
  Nil   ::                    NP f EMPTYL
  Cons  :: f x -> NP f xs ->  NP f (x (P (:)) xs)
\end{code}

\end{frame}

\begin{frame}
  \frametitle{Interpreting Codes (\texttt{generics-sop})}
\begin{code}
data I x = I x 
space
type Rep (c :: PL (PL Star))  = NS (NP I) c
\end{code}
\pause
Recall the |Tree| example:
\begin{code}
type instance Code (Tree a) = PL (EMPTYL , PL (a , Tree a , Tree a))

leaf       :: Rep (Code (Tree a))
leaf       = Here Nil

bin        :: a -> Tree a -> Tree a -> Rep (Code (Tree a))
bin e l r  = There (Here (Cons e (Cons l (Cons r Nil))))
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Writing Generic Functions}

Package it in a class
\begin{code}
class Size a where
  size :: a -> Int
\end{code}
\pause
Then write the generic infrastructure:
\begin{code}
gsize  :: (Generic x , All2 Size (Code x)) 
       => x -> Int
gsize  = goS . from
  where
    goS (Here   x) = goP x
    goS (There  x) = goS x

    goP Nil          = 0
    goP (Cons x xs)  = size x + goP xs
\end{code}
\end{frame}

%format zeta = "\HV{\zeta}"
\begin{frame}
  \frametitle{Generics of All Kinds}

   \begin{itemize}
     \itemsep2em
     \item So far, only handle types of kind |Star| with no parameters.
     \pause
     \item Consequence of little structure on |Code|s.
     \pause
     \item \emph{Solution:} Augment the language of codes!
\begin{code}
type DataType (zeta :: Kind) = PL (PL (Atom zeta (Star)))
\end{code}\vspace{-3em}
     \pause
     \item |Atom| is the applicative fragment of the $\lambda$-calculus
           with de Bruijn indices.
   \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Generics of All Kinds}

%format :@: = "\mathbin{\HT{:\!\!@\!\!:}}"
\begin{code}
data Atom (zeta :: Kind) (k :: Kind) :: (Star) where
  Var    :: TyVar zeta k                       -> Atom zeta k
  Kon    :: k                                  -> Atom zeta k
  (:@:)  :: Atom zeta (l -> k) -> Atom zeta l  -> Atom zeta k
\end{code}
\begin{overprint}
\onslide<1>
\begin{code}
data TyVar (zeta :: Kind) (k :: Kind) :: (Star) where
  VZ  ::                TyVar (x -> xs) x
  VS  :: TyVar xs k ->  TyVar (x -> xs) k
\end{code}
\onslide<2>
Going back to our |Tree| example:
\begin{code}
data Tree a = Leaf | Bin a (Tree a) (Tree a)
\end{code}
\begin{code}
type V0 = Var VZ
type TreeCode 
  = PL ( EMPTYL , PL (V0 , Kon Tree :@: V0 , Kon Tree :@: V0))
  :: PL (PL (Atom (Star -> Star) Star))
\end{code}
\end{overprint}
\end{frame}

\begin{frame}
  \frametitle{Interpreting \texttt{Atom}s}

Interpreting atoms needs environment.
%format Gamma  = "\HT{\Gamma}"
%format Gamma0 = "\HT{\epsilon}"
%format :&&:   = "\mathbin{\HT{:\!\!\&\!\!:}}"
\begin{code}
data Gamma (zeta :: Kind) where
  Gamma0  ::                   Gamma (Star)
  (:&&:)  :: k -> Gamma ks ->  Gamma (k -> ks)
\end{code}

\begin{overprint}
\onslide<2>
For example,
\begin{code}
Int :&&: Maybe :&&: Char :&&: Gamma0
\end{code}
Is a well-formed enviroment of kind
\begin{code}
Gamma (Star -> (Star -> Star) -> Star -> Star)
\end{code}
\onslide<3>
\begin{code}
type family Ty zeta (tys :: Gamma zeta) (t :: Atom zeta k) :: k where
  Ty (k -> ks) (t :&&: ts) (Var VZ)      = t
  Ty (k -> ks) (t :&&: ts) (Var (VS v))  = Ty ks ts (Var v)
  Ty zeta ts (Kon t)    = t
  Ty zeta ts (f :@: x)  = (Ty zeta ts f) (Ty zeta ts x)
\end{code}
\end{overprint}
\end{frame}

\begin{frame}

  Define |NA| and |Rep|

\end{frame}

\begin{frame}
  \frametitle{Approaching a Unified API}

  Usually, GP libraries provide a class:

\begin{code}
class Generic f where
  type Code a :: CodeKind
  from  :: f -> Rep (Code f)
  to    :: Rep (Code f)
\end{code}
\pause

  In our case, though, the number of arguments to |f| depend on it's kind!

\begin{code}
from :: f      -> Rep (Star) (Code f) Gamma0
from :: f x    -> Rep (Star) (Code f) (x :&&: Gamma0)
from :: f x y  -> Rep (Star) (Code f) (x :&&: y :&&: Gamma0)
\end{code}

\end{frame}

\begin{frame}
  \frametitle{Approaching a Unified API}

  Write a GADT:

\begin{code}
data ApplyT zeta (f :: k) (alpha :: Gamma zeta) :: Star where
  A0 :: f                   -> ApplyT (Star)     f Gamma0
  AS :: ApplyT ks (f t) ts  -> ApplyT (k -> ks)  f (t :&&: ts)
\end{code}

\pause
Which allows us to unify the interface:

\begin{code}
from :: ApplyT zeta f a -> Rep zeta (Code f) a
\end{code}

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