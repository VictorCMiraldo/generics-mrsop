{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Generics.MRSOP.Holes where

import Data.Proxy
import Data.Functor.Const
import Data.Type.Equality
import qualified Data.Set as S (insert , empty , Set)

import Control.Monad.Identity
import Control.Monad.State

import Generics.MRSOP.Base

-- * Annotating a Mutually Recursive Family with Holes

-- $withholes
--
-- It is often the case that we must perform some sort of symbolic
-- processing over our datatype. Take /unification/ for example.
-- For that to work, we must either have a dedicated constructor
-- in the datatype for representing a /metavariable/, which would
-- be difficult to access in a generic fashion, or we must augment
-- the definition an add those.
--
-- In this module we provide the 'Holes' datatype, which
-- enables this very functionality. Imagine the following
-- family:
--
-- > data Exp     = Add Exp Exp | Let Decls Exp | Var Exp
-- > data Decls   = Decl VarDecl Decls | Empty
-- > data VarDecl = VarD String Exp
--
-- The values that inhabit the type @Holes ki FamExp phi@ are
-- essentially isomorphic to:
--
-- > data Exp'     = Add Exp' Exp' | Let Decls' Exp' | Var Exp' | EHole (phi IdxExp)
-- > data Decls'   = Decl VarDecl' Decls' | Empty | DHole (phi IdxDecls)
-- > data VarDecl' = VarD String Exp' | VHole (phi IdxVarDecl)
--
-- If we want to, say, forbid holes on the declaration bit, we
-- can do so in the definition of phi. For example:
--
-- > data OnlyExpAndVarHoles :: Atom kon -> * where
-- >   ExpHole :: OnlyExpAndVarHoles ('I IdxExp)
-- >   VarHole :: OnlyExpAndVarHoles ('I IdxVar)
--
-- 

-- |A value of type 'HolesAnn' augments a mutually recursive
--  family with holes. This is useful for writing generic
--  unification-like algorithms.
--
--  Essentially, we have the following isomorphism:
--
--  > Holes ann ki codes phi at
--  >   =~= (ann at :*: (phi :+: NA ki (Rep ki (Holes ann ki codes phi))))
--
--  That is, we are extending the representations with values of
--  type @phi@, and adding annotations of type @ann at@ everywhere.
--  A simpler variant of this type is given in 'Holes', where
--  the annotationsare defaulted to @Const ()@
--
--  The annotations are ignored in most of the functions and are here
--  only as a means of helping algorithms keep intermediate values
--  directly in the datatype. They have no semantic meaning.
--
--  Note that @HolesAnn ann ki codes@, of kind @(Atom kon -> *) -> Atom kon -> *@
--  forms an indexed free monad.
data HolesAnn :: (Atom kon -> *)
              -> (kon -> *)
              -> [[[Atom kon]]]
              -> (Atom kon -> *)
              -> Atom kon
              -> *
    where
  -- |A "hole" contains something of type @phi@ 
  Hole  :: ann at -> phi at -> HolesAnn ann ki codes phi at
  -- |An opaque value
  HOpq  :: ann ('K k) -> ki k   -> HolesAnn ann ki codes phi ('K k) 
  -- |A view over a constructor with its fields replaced
  --  by treefixes. This already comes in a SOP flavour.
  HPeel :: (IsNat n , IsNat i)
        => ann ('I i)
        -> Constr (Lkup i codes) n 
        -> NP (HolesAnn ann ki codes phi) (Lkup n (Lkup i codes))
        -> HolesAnn ann ki codes phi ('I i)

-- |Extracts the annotation from the topmost 'HolesAnn' constructor.
holesAnn :: HolesAnn ann ki codes phi at -> ann at
holesAnn (Hole a _)    = a
holesAnn (HOpq a _)    = a
holesAnn (HPeel a _ _) = a

-- * Mapping Over 'HolesAnn'

-- |Our 'HolesAnn' is a higher order functor and can be mapped over.
holesMapAnnM :: (Monad m)
             => (forall a . f a   -> m (g a))    -- ^ Function to map over holes
             -> (forall a . ann a -> m (bnn a))  -- ^ Function to map over annotations
             -> HolesAnn ann ki codes f at
             -> m (HolesAnn bnn ki codes g at)
holesMapAnnM f g (Hole  a x)   = Hole <$> g a <*> f x
holesMapAnnM _ g (HOpq  a k)   = flip HOpq k <$> g a
holesMapAnnM f g (HPeel a c p) = g a >>= \a' -> HPeel a' c <$> mapNPM (holesMapAnnM f g) p

-- |Maps over the index part, not the annotation
holesMapM :: (Monad m)
          => (forall a . f a -> m (g a))
          -> HolesAnn ann ki codes f at
          -> m (HolesAnn ann ki codes g at)
holesMapM f = holesMapAnnM f return

-- |Non-monadic version of 'holesMapM'
holesMapAnn :: (forall a . f   a -> g    a)
            -> (forall a . ann a -> ann' a)
            -> HolesAnn ann  ki codes f at
            -> HolesAnn ann' ki codes g at
holesMapAnn f g = runIdentity . holesMapAnnM (return . f) (return . g)

-- |Non-monadic version of 'holesMapM'
holesMap :: (forall a . f a -> g a)
         -> HolesAnn ann ki codes f at
         -> HolesAnn ann ki codes g at
holesMap f = holesMapAnn f id

-- |Since 'HolesAnn' is just a free monad, we can join them!
holesJoin :: HolesAnn ann ki codes (HolesAnn ann ki codes f) at
          -> HolesAnn ann ki codes f at
holesJoin (Hole _ x)    = x
holesJoin (HOpq a k)    = HOpq a k 
holesJoin (HPeel a c p) = HPeel a c (mapNP holesJoin p)

-- * Extracting Annotations and HolesAnn from 'HolesAnn'

-- |Returns the set of holes in a value of type 'HolesAnn'. The _getter_
-- argument is there to handle the existantial type index present
-- in the holes and the insertion function is used to place
-- the holes in a datastructure of choice. The treefix is taversed
-- in a pre-order style and the holes inserted in the sturcture
-- as they are visited.
holesGetHolesAnnWith :: forall f r ann ki codes phi at
                      . f r                           -- ^ Empty structure
                     -> (r -> f r -> f r)             -- ^ Insertion function
                     -> (forall ix . phi ix -> r)     -- ^ How to get rid of the existential type
                     -> HolesAnn ann ki codes phi at 
                     -> f r
holesGetHolesAnnWith empty ins tr
  = flip execState empty . holesMapM getHole
  where
    getHole :: phi ix
            -> State (f r) (phi ix)
    getHole x = modify (ins $ tr x) >> return x

-- |Instantiates 'holesGetHolesAnnWith' to use a list.
-- It's implementation is trivial:
--
-- > holesGetHolesAnnWith' = holesGetHolesAnnWith [] (:)
holesGetHolesAnnWith' :: (forall ix . phi ix -> r)
                      -> HolesAnn ann ki codes phi at -> [r]
holesGetHolesAnnWith' = holesGetHolesAnnWith [] (:)

-- |Instantiates 'holesGetHolesAnnWith' to use a set instead of a list.
holesGetHolesAnnWith'' :: (Ord r)
                       => (forall ix . phi ix -> r)
                       -> HolesAnn ann ki codes phi at -> S.Set r
holesGetHolesAnnWith'' = holesGetHolesAnnWith S.empty S.insert

-- * Refining 'HolesAnn'

-- |Similar to 'holesMapM', but allows to refine the structure of
--  a treefix if need be. One could implement 'holesMapM' as:
--
--  > holesMapM f = holesRefineAnn (\a h -> Hole a <$> f h) HOpq'
--
holesRefineAnnM :: (Monad m)
                => (forall ix . ann ix     -> f ix -> m (HolesAnn ann ki codes g ix))
                -> (forall k  . ann ('K k) -> ki k -> m (HolesAnn ann ki codes g ('K k)))
                -> HolesAnn ann ki codes f at
                -> m (HolesAnn ann ki codes g at)
holesRefineAnnM f _ (Hole a x) = f a x
holesRefineAnnM _ g (HOpq a k) = g a k
holesRefineAnnM f g (HPeel a c holesnp)
  = HPeel a c <$> mapNPM (holesRefineAnnM f g) holesnp

-- |Just like 'holesRefineAnnM', but only refines variables. One example is to implement
-- 'holesJoin' with it.
--
-- > holesJoin = runIdentity . holesRefineVarsM (\_ -> return)
--
holesRefineVarsM :: (Monad m)
                 => (forall ix . ann ix -> f ix -> m (HolesAnn ann ki codes g ix)) -- ^ How to produce a 'HolesAnn' from the previous hole.
                 -> HolesAnn ann ki codes f at
                 -> m (HolesAnn ann ki codes g at)
holesRefineVarsM f = holesRefineAnnM f (\a -> return . HOpq a)

-- |Pure version of 'holesRefineAnnM'
holesRefineAnn :: (forall ix . ann ix     -> f ix -> HolesAnn ann ki codes g ix) -- ^
               -> (forall k  . ann ('K k) -> ki k -> HolesAnn ann ki codes g ('K k))
               -> HolesAnn ann ki codes f at 
               -> HolesAnn ann ki codes g at
holesRefineAnn f g = runIdentity . holesRefineAnnM (\a -> return . f a) (\a -> return . g a)

-- * Annotation Catamorphism and Synthesized Attributes

-- |Standard monadic catamorphism for holes. The algebra can take the
--  annotation into account.
holesAnnCataM :: (Monad m)
              => (forall at  . ann at     -> phi at -> m (res at))      -- ^ Action to perform at 'Hole'
              -> (forall k   . ann ('K k) -> ki k   -> m (res ('K k)))  -- ^ Action to perform at 'HOpq'
              -> (forall i n . (IsNat i, IsNat n)
                            => ann ('I i) -> Constr (Lkup i codes) n
                                          -> NP res (Lkup n (Lkup i codes))
                                          -> m (res ('I i)))            -- ^ Action to perform at 'HPeel'
              -> HolesAnn ann ki codes phi ix
              -> m (res ix)
holesAnnCataM hF _  _  (Hole a x) = hF a x
holesAnnCataM _  oF _  (HOpq a x) = oF a x
holesAnnCataM hF oF cF (HPeel a c p)
  = mapNPM (holesAnnCataM hF oF cF) p >>= cF a c 

-- |Pure variant of 'holesAnnCataM'
holesAnnCata :: (forall at  . ann at     -> phi at -> res at)     -- ^ Action to perform at 'Hole'
             -> (forall k   . ann ('K k) -> ki k   -> res ('K k)) -- ^ Action to perform at 'HOpq'
             -> (forall i n . (IsNat i, IsNat n)
                           => ann ('I i) -> Constr (Lkup i codes) n
                                         -> NP res (Lkup n (Lkup i codes))
                                         -> res ('I i))           -- ^ Action to perform at 'HPeel'
             -> HolesAnn ann ki codes phi ix
             -> res ix
holesAnnCata hF oF cF = runIdentity
                      . holesAnnCataM (\a phi -> return $ hF a phi)
                                      (\a o   -> return $ oF a o)
                                      (\a c p -> return $ cF a c p)

-- |Synthesizes attributes over a value of type 'HolesAnn'. This
-- is extremely useful for easily annotating a value with auxiliar
-- annotations.
holesSynthesizeM :: (Monad m)
                 => (forall at  . ann at     -> phi at -> m (res at))     -- ^ Action to perform at 'Hole'
                 -> (forall k   . ann ('K k) -> ki k   -> m (res ('K k))) -- ^ Action to perform at 'HOpq'
                 -> (forall i n . (IsNat i, IsNat n)
                              => ann ('I i) -> Constr (Lkup i codes) n
                                            -> NP res (Lkup n (Lkup i codes))
                                            -> m (res ('I i)))            -- ^ Action to perform at 'HPeel'
                 -> HolesAnn ann  ki codes phi atom                       -- ^ Input value
                 -> m (HolesAnn res ki codes phi atom)
holesSynthesizeM hF oF cF
  = holesAnnCataM (\a phi -> flip Hole phi <$> hF a phi)
                  (\a o   -> flip HOpq o   <$> oF a o)
                  (\a c p -> (\r -> HPeel r c p) <$> cF a c (mapNP holesAnn p))

-- |Pure variant of 'holesSynthesize'
holesSynthesize :: (forall at  . ann at     -> phi at -> res at) -- ^
                -> (forall k   . ann ('K k) -> ki k   -> res ('K k))
                -> (forall i n . (IsNat i, IsNat n)
                              => ann ('I i) -> Constr (Lkup i codes) n
                                            -> NP res (Lkup n (Lkup i codes))
                                            -> res ('I i))
             -> HolesAnn ann ki codes phi ix
             -> HolesAnn res ki codes phi ix
holesSynthesize hF oF cF = runIdentity
                         . holesSynthesizeM (\a phi -> return $ hF a phi)
                                            (\a o   -> return $ oF a o)
                                            (\a c p -> return $ cF a c p)

-- * Using 'Holes' with no annotations

-- |Ignoring the annotations is easy; just use
--  @Const ()@
type Holes = HolesAnn (Const ())

-- |Synonym to @Hole (Const ())@
pattern Hole' :: phi at -> Holes ki codes phi at
pattern Hole' x = Hole (Const ()) x


-- |Synonym to @HOpq (Const ())@
pattern HOpq' :: (at ~ 'K k) => ki k -> Holes ki codes phi at
pattern HOpq' x = HOpq (Const ()) x


-- |Synonym to @HPeel (Const ())@
pattern HPeel' :: (at ~ 'I i) => (IsNat n, IsNat i)
               => Constr (Lkup i codes) n
               -> NP (Holes ki codes phi) (Lkup n (Lkup i codes))
               -> Holes ki codes phi at
pattern HPeel' c p = HPeel (Const ()) c p

{-# COMPLETE Hole' , HOpq' , HPeel' #-}

-- |Factors out the largest common prefix of two treefixes.
--  This is also known as the anti-unification of two
--  treefixes.
--
--  It enjoys naturality properties with holesJoin:
--
--  >  holesJoin (holesMap fst (holesLCP p q)) == p
--  >  holesJoin (holesMap snd (holesLCP p q)) == q
--
--  We use a function to combine annotations in case it is
--  necessary.
holesLCP :: (EqHO ki)
         => Holes ki codes f at
         -> Holes ki codes g at
         -> Holes ki codes (Holes ki codes f :*: Holes ki codes g) at
holesLCP (HOpq _ kx) (HOpq _ ky)
  | eqHO kx ky = HOpq' kx
  | otherwise  = Hole' (HOpq' kx :*: HOpq' ky)
holesLCP (HPeel a cx px) (HPeel b cy py)
  = case testEquality cx cy of
      Nothing   -> Hole'  (HPeel a cx px :*: HPeel b cy py)
      Just Refl -> HPeel' cx $ mapNP (uncurry' holesLCP) (zipNP px py)
holesLCP x y = Hole' (x :*: y)

-- * Translating between 'NA' and 'HolesAnn'

-- |A stiff treefix is one with no holes anywhere.
na2holes :: NA ki (Fix ki codes) at -> HolesAnn (Const ()) ki codes f at
na2holes (NA_K k) = HOpq' k
na2holes (NA_I x) = case sop (unFix x) of
  Tag cx px -> HPeel' cx (mapNP na2holes px)

-- |Reduces a treefix back to a tree; we use a monadic
--  function here to allow for custom failure confitions.
holes2naM :: (Monad m)
          => (forall ix . f ix -> m (NA ki (Fix ki codes) ix)) -- ^
          -> Holes ki codes f at
          -> m (NA ki (Fix ki codes) at)
holes2naM red (Hole  _ x)   = red x
holes2naM _   (HOpq  _ k)   = return (NA_K k)
holes2naM red (HPeel _ c p) = (NA_I . Fix . inj c) <$> mapNPM (holes2naM red) p

-- |Returns how many holes are inside a treefix
holesArity :: HolesAnn ann ki codes f at -> Int
holesArity = length . holesGetHolesAnnWith' (const ())

-- |Returns the size of a treefix. Holes have size 0.
holesSize :: HolesAnn ann ki codes f at -> Int
holesSize (Hole _ _)    = 0
holesSize (HOpq _  _)   = 1
holesSize (HPeel _ _ p) = 1 + sum (elimNP holesSize p)

-- |Returns the singleton identifying the index of a 'HolesAnn'
holesSNat :: (IsNat ix)
          => HolesAnn ann ki codes f ('I ix)
          -> SNat ix
holesSNat _ = getSNat (Proxy :: Proxy ix)

-- -* Instances

instance (EqHO phi , EqHO ki) => EqHO (Holes ki codes phi) where
  eqHO utx uty = and $ holesGetHolesAnnWith' (uncurry' cmp) $ holesLCP utx uty
    where
      cmp :: HolesAnn ann ki codes phi at -> HolesAnn ann ki codes phi at -> Bool
      cmp (Hole _ x) (Hole _ y) = x `eqHO` y
      cmp (HOpq _ x) (HOpq _ y) = x `eqHO` y
      cmp _           _         = False

holesShow :: forall ki ann f fam codes ix
           . (HasDatatypeInfo ki fam codes , ShowHO ki , ShowHO f)
          => Proxy fam
          -> (forall at . ann at -> ShowS)
          -> HolesAnn ann ki codes f ix
          -> ShowS
holesShow _ f (Hole a x)       = showParen True $ f a . showString (showHO x) 
holesShow _ f (HOpq a k)       = showParen True $ f a . showString (showHO k)
holesShow p f h@(HPeel a c rest)
  = showParen (needParens h) $ showString cname
                             . f a
                             . showString " "
                             . withSpaces (elimNP (holesShow p f) rest)
  where
    withSpaces :: [ShowS] -> ShowS
    withSpaces ls = foldl (\r ss -> r . showString " " . ss) id ls
    
    cname = case constrInfoFor p (holesSNat h) c of
      (Record name _)    -> name
      (Constructor name) -> name
      (Infix name _ _)   -> "(" ++ name ++ ")"
 
    needParens :: HolesAnn ann ki codes f iy -> Bool
    needParens (Hole _ _)      = False
    needParens (HOpq _ _)      = False
    needParens (HPeel _ _ Nil) = False
    needParens _               = True

instance (HasDatatypeInfo ki fam codes , ShowHO ki , ShowHO f)
    => Show (Holes ki codes f at) where
  show h = holesShow (Proxy :: Proxy fam) (const id) h ""
