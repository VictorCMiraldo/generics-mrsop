{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE PolyKinds         #-}
-- | Standard representation of n-ary products.
module Generics.MRSOP.Base.NP where

import Generics.MRSOP.Util

infixr 5 :*
-- |Indexed n-ary products. This is analogous to the @All@ datatype
--  in Agda. 
data NP :: (k -> *) -> [k] -> * where
  NP0  :: NP p '[]
  (:*) :: p x -> NP p xs -> NP p (x : xs)

instance EqHO phi => EqHO (NP phi) where
  eqHO = eqNP eqHO

instance EqHO phi => Eq (NP phi xs) where
  (==) = eqHO

instance ShowHO phi => ShowHO (NP phi) where
  showHO NP0 = "NP0"
  showHO (a :* b) = showHO a ++ " :* " ++ showHO b

instance ShowHO phi => Show (NP phi xs) where
  show = showHO

-- * Relation to IsList predicate

-- |Append two values of type 'NP'
appendNP :: NP p xs -> NP p ys -> NP p (xs :++: ys)
appendNP NP0        ays = ays
appendNP (a :* axs) ays = a :* appendNP axs ays

-- |Proves that the index of a value of type 'NP' is a list.
--  This is useful for pattern matching on said list without
--  having to carry the product around.
listPrfNP :: NP p xs -> ListPrf xs
listPrfNP NP0       = Nil
listPrfNP (_ :* xs) = Cons $ listPrfNP xs

-- * Map, Elim and Zip

-- |Maps a natural transformation over a n-ary product
mapNP :: f :-> g -> NP f ks -> NP g ks
mapNP _ NP0       = NP0
mapNP f (k :* ks) = f k :* mapNP f ks

-- |Maps a monadic natural transformation over a n-ary product
mapNPM :: (Monad m) => (forall x . f x -> m (g x)) -> NP f ks -> m (NP g ks)
mapNPM _ NP0       = return NP0
mapNPM f (k :* ks) = (:*) <$> f k <*> mapNPM f ks

-- |Eliminates the product using a provided function.
elimNP :: (forall x . f x -> a) -> NP f ks -> [a]
elimNP _ NP0       = []
elimNP f (k :* ks) = f k : elimNP f ks

-- |Monadic eliminator
elimNPM :: (Monad m) => (forall x . f x -> m a) -> NP f ks -> m [a]
elimNPM _ NP0       = return []
elimNPM f (k :* ks) = (:) <$> f k <*> elimNPM f ks

-- |Combines two products into one.
zipNP :: NP f xs -> NP g xs -> NP (f :*: g) xs
zipNP NP0       NP0       = NP0
zipNP (f :* fs) (g :* gs) = (f :*: g) :* zipNP fs gs

-- |Unzips a combined product into two separate products
unzipNP :: NP (f :*: g) xs -> (NP f xs , NP g xs)
unzipNP NP0               = (NP0 , NP0) 
unzipNP (Pair f g :* fgs) = (f :*) *** (g :*) $ unzipNP fgs

-- * Catamorphism

-- |Consumes a value of type 'NP'.
cataNP :: (forall a as . f a  -> r as -> r (a : as))
       -> r '[]
       -> NP f xs -> r xs
cataNP _fCons fNil NP0       = fNil
cataNP fCons  fNil (k :* ks) = fCons k (cataNP fCons fNil ks)

-- |Consumes a value of type 'NP'.
cataNPM :: (Monad m)
        => (forall a as . f a  -> r as -> m (r (a : as)))
        -> m (r '[])
        -> NP f xs -> m (r xs)
cataNPM _fCons fNil NP0       = fNil
cataNPM fCons fNil (k :* ks) = cataNPM fCons fNil ks >>= fCons k 


-- * Equality

-- |Compares two 'NP's pairwise with the provided function and
--  return the conjunction of the results.
eqNP :: (forall x. p x -> p x -> Bool)
     -> NP p xs -> NP p xs -> Bool
eqNP p x = and . elimNP (uncurry' p) . zipNP x

