{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# OPTIONS_GHC -cpp         #-}
{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Provides a simple way for the end-user deriving
--   the mechanical, yet long, Element instances
--   for a family.
--
--   We are borrowing a lot of code from generic-sop
--   ( https://hackage.haskell.org/package/generics-sop-0.3.2.0/docs/src/Generics-SOP-TH.html )
--
module Generics.MRSOP.TH (deriveFamily, genFamilyDebug) where

import Data.Function (on)
import Data.List (sortBy)

import Control.Arrow ((***), (&&&))
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (liftString)

import Generics.MRSOP.Konstants
import Generics.MRSOP.Base.Class
import Generics.MRSOP.Base.Internal.NS
import Generics.MRSOP.Base.Internal.NP
import Generics.MRSOP.Base.Universe

import qualified Data.Map as M

-- |Given the name of the first element in the family,
--  derives:
--
--    1. The other types in the family and Konstant types one needs.
--    2. the SOP code for each of the datatypes involved
--    3. One 'Element' instance per datatype
--    TODO: 4. Metadada information for each of the datatypes involved
deriveFamily :: Q Type -> Q [Dec]
deriveFamily t
  = do sty              <- t >>= convertType 
       (_ , (Idxs _ m)) <- runIdxsM (reifySTy sty)
       -- Now we make sure we have processed all
       -- types
       m' <- mapM extractDTI (M.toList m)
       let final = sortBy (compare `on` second) m' 
       dbg <- genFamilyDebug sty m'
       res <- genFamily sty m'
       return (dbg ++ res)
  where
    second (_ , x , _) = x
    
    extractDTI (sty , (ix , Nothing))
      = fail $ "Type " ++ show sty ++ " has no datatype information."
    extractDTI (sty , (ix , Just dti))
      = return (sty , ix , dti)

-- Sketch;
--
--   Given a module:
--
--    > module Test where
--    > data Rose a = Fork a [Rose a]
--    > $(deriveFamily [t| Rose Int |])
--
--  We will see we are looking into deriving a family
--  for an AppT (ConT Rose) (ConT Int).
--
--  Working with a (M.Map STy (Int , DInfo (K + I))) in a state;
--
--  0) Translate to a simpler Type-expression, call it STy.
--  1) Register (AppST (ConST Rose) (ConST Int)) as family index Z
--  2) reify lhs: [d| data Rose a = Fork a [Rose a] |]
--      a) reduce rhs of (1): (\a -> Fork a [Rose a]) @ (ConT Int)
--                        == Fork Int [Rose Int]
--      b) Take the fields that require processing: [ConT Int , AppST List (AppST Rose Int)]
--      c) Somehow figure out that (ConT Int) is a Konstant.
--      d) Look into (AppST List (AppST Rose Int))
--      e) Is it already processed?
--      f) If yes, we are done.
--  3) Register (AppST List (AppST Rose Int))as family index (S Z)
--  4) reify lhs: [d| data List a = Nil | Cons a (List a) |]
--      a) reduce rhs of (4): (\a -> Nil | Cons a (List a)) @ (AppST Rose Int)
--      b) Take the fields of each constructor:
--           [] , [AppST Rose Int , AppST List (AppST Rose Int)]
--      c) Notice that both fields of 'Cons' have already
--         been registered; hence they become: [I Z , I (S Z)]
--

-- * Data Structures

type DataName  = Name
type ConName   = Name
type FieldName = Name
type Args      = [Name]

-- |Datatype information, parametrized by the type of Type-expressions
--  that appear on the fields of the constructors.
data DTI ty
  = ADT DataName Args [ CI ty ]
  | New DataName Args (CI ty)
  deriving (Eq , Show , Functor)

-- |Constructor information
data CI ty
  = Normal ConName [ty]
  | Infix  ConName ty ty
  | Record ConName [ (FieldName , ty) ]
  deriving (Eq , Show , Functor)

-- ** Monadic Maps

ciMapM :: (Monad m) => (ty -> m tw) -> CI ty -> m (CI tw)
ciMapM f (Normal name tys) = Normal name <$> mapM f tys
ciMapM f (Infix name l r)  = Infix name <$> f l <*> f r
ciMapM f (Record name tys) = Record name <$> mapM (rstr . (id *** f)) tys
  where
    rstr (a , b) = b >>= return . (a,)

dtiMapM :: (Monad m) => (ty -> m tw) -> DTI ty -> m (DTI tw)
dtiMapM f (ADT name args ci) = ADT name args <$> mapM (ciMapM f) ci
dtiMapM f (New name args ci) = New name args <$> ciMapM f ci

dti2ci :: DTI ty -> [CI ty]
dti2ci (ADT _ _ cis) = cis
dti2ci (New _ _ ci)  = [ ci ]

ci2ty :: CI ty -> [ty]
ci2ty (Normal _ tys) = tys
ci2ty (Infix _ a b)  = [a , b]
ci2ty (Record _ tys) = map snd tys

ciName :: CI ty -> Name
ciName (Normal n _)  = n
ciName (Infix n _ _) = n
ciName (Record n _)  = n

ci2Pat :: CI ty -> Q ([Name] , Pat)
ci2Pat ci
  = do ns <- mapM (const (newName "x")) (ci2ty ci)
       return (ns , (ConP (ciName ci) (map VarP ns)))

-- * Simpler STy Language

-- A Simplified version of Language.Haskell.TH
data STy
  = AppST STy STy
  | VarST Name
  | ConST Name
  deriving (Eq , Show, Ord)

styFold :: (a -> a -> a) -> (Name -> a) -> (Name -> a) -> STy -> a
styFold app var con (AppST a b) = app (styFold app var con a) (styFold app var con b)
styFold app var con (VarST n)   = var n
styFold app var con (ConST n)   = con n

-- |Does a STy have a varible name?
isClosed :: STy -> Bool
isClosed = styFold (&&) (const False) (const True)

-- ** Back and Forth conversion

convertType :: (Monad m) => Type -> m STy
convertType (AppT a b)  = AppST <$> convertType a <*> convertType b
convertType (SigT t _)  = convertType t
convertType (VarT n)    = return (VarST n)
convertType (ConT n)    = return (ConST n)
convertType (ParensT t) = convertType t
convertType ListT       = return (ConST (mkName "[]"))
convertType t           = fail ("convertType: Unsupported Type: " ++ show t)

trevnocType :: STy -> Type
trevnocType (AppST a b) = AppT (trevnocType a) (trevnocType b)
trevnocType (VarST n)   = VarT n
trevnocType (ConST n)
  | n == mkName "[]" = ListT
  | otherwise        = ConT n

-- |Handy substitution function.
--
--  @stySubst t m n@ substitutes m for n within t, that is: t[m/n]
stySubst :: STy -> Name -> STy -> STy
stySubst (AppST a b) m n = AppST (stySubst a m n) (stySubst b m n)
stySubst (ConST a)   m n = ConST a
stySubst (VarST x)   m n
  | x == m    = n
  | otherwise = VarST x

-- |Just like subst, but applies a list of substitutions
styReduce :: [(Name , STy)] -> STy -> STy
styReduce parms t = foldr (\(n , m) ty -> stySubst ty n m) t parms

-- |Flattens an application into a list of arguments;
--
--  @styFlatten (AppST (AppST Tree A) B) == (Tree , [A , B])@
styFlatten :: STy -> (STy , [STy])
styFlatten (AppST a b) = id *** (++ [b]) $ styFlatten a
styFlatten sty         = (sty , [])

-- * Parsing Haskell's AST

reifyDec :: Name -> Q Dec
reifyDec name =
  do info <- reify name
     case info of TyConI dec -> return dec
                  _          -> fail $ show name ++ " is not a declaration"

argInfo :: TyVarBndr -> Name
argInfo (PlainTV  n)   = n
argInfo (KindedTV n _) = n

-- Extracts a DTI from a Dec
decInfo :: Dec -> Q (DTI STy)
decInfo (TySynD     name args      ty)     = fail "Type Synonyms not supported"
decInfo (DataD    _ name args    _ cons _) = ADT name (map argInfo args) <$> mapM conInfo cons
decInfo (NewtypeD _ name args    _ con _)  = New name (map argInfo args) <$> conInfo con
decInfo _                                  = fail "Only type declarations are supported"

-- Extracts a CI from a Con
conInfo :: Con -> Q (CI STy)
conInfo (NormalC  name ty) = Normal name <$> mapM (convertType . snd) ty
conInfo (RecC     name ty) = Record name <$> mapM (\(s , _ , t) -> (s,) <$> convertType t) ty
conInfo (InfixC l name r)
  = do info <- reifyFixity name
       case info of
         -- TODO: incorporate fixity information.
         _ -> Infix name <$> convertType (snd l) <*> convertType (snd r)
conInfo (ForallC _ _ _) = fail "Existentials not supported"
#if MIN_VERSION_template_haskell(2,11,0)
conInfo (GadtC _ _ _)    = fail "GADTs not supported"
conInfo (RecGadtC _ _ _) = fail "GADTs not supported"
#endif

-- |Reduces the rhs of a datatype declaration
--  with some provided arguments. Step (2.a) of our sketch.
--
--  Precondition: application is fully saturated;
--  ie, args and parms have the same length
--
dtiReduce :: DTI STy -> [STy] -> DTI STy
dtiReduce (ADT name args cons) parms
  = ADT name [] (map (ciReduce (zip args parms)) cons)
dtiReduce (New name args con)  parms
  = New name [] (ciReduce (zip args parms) con)

ciReduce :: [(Name , STy)] -> CI STy -> CI STy
ciReduce parms ci = runIdentity (ciMapM (return . styReduce parms) ci)  

-- * Monad
--
-- Keeks the (M.Map STy (Int , DTI Sty)) in a state.

data IK
  = AtomI Int
  | AtomK Name
  deriving (Eq , Show)

data Idxs 
  = Idxs { idxsNext :: Int
         , idxsMap  :: M.Map STy (Int , Maybe (DTI IK))
         }
  deriving (Show)

onMap :: (M.Map STy (Int , Maybe (DTI IK)) -> M.Map STy (Int , Maybe (DTI IK)))
      -> Idxs -> Idxs
onMap f (Idxs n m) = Idxs n (f m)

type IdxsM = StateT Idxs

runIdxsM :: (Monad m) => IdxsM m a -> m (a , Idxs)
runIdxsM = flip runStateT (Idxs 0 M.empty)

-- |The actual monad we need to run all of this;
type M = IdxsM Q

-- |Returns the index of a "Name" within the family.
--  If this name has not been registered yet, returns
--  a fresh index.
indexOf :: (Monad m) => STy -> IdxsM m Int
indexOf name
  = do st <- get
       case M.lookup name (idxsMap st) of
         Just i  -> return (fst i)
         Nothing -> let i = idxsNext st
                     in put (Idxs (i + 1) (M.insert name (i , Nothing) (idxsMap st)))
                     >> return i

-- |Register some Datatype Information for a given STy
register :: (Monad m) => STy -> DTI IK -> IdxsM m ()
register ty info = indexOf ty -- the call to indexOf guarantees the
                              -- adjust will do something;
                >> modify (onMap $ M.adjust (id *** const (Just info)) ty)

-- | All the necessary lookups:
lkup :: (Monad m) => STy -> IdxsM m (Maybe (Int , Maybe (DTI IK)))
lkup ty = M.lookup ty . idxsMap <$> get

lkupInfo :: (Monad m) => STy -> IdxsM m (Maybe Int)
lkupInfo ty = fmap fst <$> lkup ty

lkupData :: (Monad m) => STy -> IdxsM m (Maybe (DTI IK))
lkupData ty = join . fmap snd <$> lkup ty

hasData :: (Monad m) => STy -> IdxsM m Bool
hasData ty = maybe False (const True) <$> lkupData ty

----------------------------
-- * Preprocessing Data * --
----------------------------

-- |Performs step 2 of the sketch;
reifySTy :: STy -> M ()
reifySTy sty
  =  indexOf sty
  >> uncurry go (styFlatten sty)
  where
    go :: STy -> [STy] -> M ()
    go (ConST name) args
      = do dec <- lift (reifyDec name >>= decInfo)
           -- TODO: Check that the precondition holds.
           let res = dtiReduce dec args
           (final , todo) <- runWriterT $ dtiMapM convertSTy res
           register sty final
           mapM_ reifySTy todo
    
    -- Convert the STy's in the fields of the constructors;
    -- tells a list of STy's we still need to process.
    convertSTy :: STy -> WriterT [STy] M IK
    convertSTy ty
      -- We remove sty from the list of todos
      -- otherwise we get an infinite loop
      | ty == sty = AtomI <$> lift (indexOf ty)
      | isClosed ty
      = case makeCons ty of
          Just k  -> return (AtomK k)
          Nothing -> do ix     <- lift (indexOf ty)
                        hasDti <- lift (hasData ty)
                        when (not hasDti) (tell [ty])
                        return (AtomI ix)
      | otherwise
      = fail $ "I can't convert type variable " ++ show ty
              ++ " when converting " ++ show sty

    makeCons :: STy -> Maybe Name
    makeCons (ConST n) = M.lookup n consTable
    makeCons _         = Nothing

    consTable = M.fromList . map (id *** mkName)
      $ [ ( ''Int     , "KInt")
        , ( ''Char    , "KChar")
        , ( ''Integer , "KInteger")
        , ( ''Float   , "KFloat")
        , ( ''Bool    , "KBool")
        , ( ''String  , "KString")
        , ( ''Double  , "KDouble")
        ]

-----------------------------
-- * Generating the Code * --
-----------------------------

-- |@genFamily init fam@ generates a type-level list
--  of the codes for the family. It also generates
--  the necessary 'Element' instances.
--  TODO: generate the 'HasDatatypeInfo' instances too!
--
--  Precondition, input is sorted on second component.
genFamily :: STy -> [(STy , Int , DTI IK)] -> Q [Dec]  
genFamily first ls
  = do fam <- familyDecl
       r   <- [d| ty :: String
                  ty = $(liftString $ show fam) |]
       name <- familyName
       els  <- concat <$> mapM (\(sty , ix , dti) -> genElement name sty ix dti) ls 
       return (fam:r ++ els)
       
  where
    familyName :: Q Name
    familyName = return . mkName
               $ ("Fam_" ++)
               $ styFold (\a -> (a ++) . ('_':)) nameBase nameBase first

    familyDecl :: Q Dec
    familyDecl = TySynD <$> familyName <*> return [] <*> familyTys

    familyTys :: Q Type
    familyTys = return $ tlListOf_l dti2Type (map (\(_ , _ , t) -> t) ls) 

-- Generates a type-level list of 'a's
tlListOf_l :: (a -> Type) -> [a] -> Type
tlListOf_l f = foldl (\r h -> AppT (AppT PromotedConsT (f h)) r) PromotedNilT

tlListOf_r :: (a -> Type) -> [a] -> Type
tlListOf_r f = foldr (\h r -> AppT (AppT PromotedConsT (f h)) r) PromotedNilT

dti2Type :: DTI IK -> Type
dti2Type = tlListOf_r ci2Type . dti2ci

ci2Type :: CI IK -> Type
ci2Type = tlListOf_r ik2Type . ci2ty

int2Type :: Int -> Type
int2Type 0 = tyZ
int2Type n = AppT tyS (int2Type (n - 1))

tyS = PromotedT (mkName "S")
tyZ = PromotedT (mkName "Z")
tyI = PromotedT (mkName "I")
tyK = PromotedT (mkName "K")

ik2Type :: IK -> Type
ik2Type (AtomI n) = AppT tyI $ int2Type n
ik2Type (AtomK k) = AppT tyK $ PromotedT k

-- |@genElement sty ix dti@ generates the instance
--  for the 'Element' class.
genElement :: Name -> STy -> Int -> DTI IK -> Q [Dec]
genElement fam sty ix dti
  = [d| instance Element Singl
                         $(return (ConT fam))
                         $(return $ int2Type ix)
                         $(return (trevnocType sty))
          where
            from = $(genFrom dti)
            to   = $(genTo dti)
      |]                       
  where
    genFrom :: DTI IK -> Q Exp
    genFrom dti = LamCaseE <$> mapM (uncurry genFromMatch) (zip [0..] (dti2ci dti))

    genFromMatch :: Int -> CI IK -> Q Match
    genFromMatch ni ci
      = do (vars , pat) <- ci2Pat ci
           bdy <- [e| Fix (Rep $(genFromExp ni (zip vars (ci2ty ci)))) |]
           return (Match pat (NormalB bdy) [])

    genFromExp :: Int -> [(Name , IK)] -> Q Exp
    genFromExp 0 ns = [e| Here $(go ns) |]
      where
        go []                   = [e| NP0 |]
        go (x : xs)             = [e| $(mkHead x) :* ( $(go xs) ) |]

        mkHead (x , AtomI _) = [e| NA_I (from $(return (VarE x))) |]
        mkHead (x , AtomK k) = [e| NA_K $(return (AppE (ConE (mkK k)) (VarE x))) |]

        mkK k = mkName $ 'S':tail (nameBase k)
    genFromExp n ns = [e| There $(genFromExp (n-1) ns) |]

    genTo   dti = [e| undefined |]

-- |Generates a bunch of strings for debug purposes.
genFamilyDebug :: STy -> [(STy , Int , DTI IK)] -> Q [Dec]
genFamilyDebug _ ms = concat <$> mapM genDec ms
  where
    genDec :: (STy , Int , DTI IK) -> Q [Dec]
    genDec (sty , ix , dti)
      = [d| $( genPat ix ) = $(mkBody dti) |]

    mkBody :: DTI IK -> Q Exp
    mkBody dti = [e| $(liftString $ show dti) |]

    genPat :: Int -> Q Pat
    genPat n = genName n >>= \name -> return (VarP name)

    genName :: Int -> Q Name
    genName n = return (mkName $ "tyInfo_" ++ show n)

test = [e| case l of
             []        -> 0
             ((:) x y) -> 1 |]
