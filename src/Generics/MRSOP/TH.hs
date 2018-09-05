{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -cpp           #-}
-- | Provides a simple way for the end-user deriving
--   the mechanical, yet long, Element instances
--   for a family.
--
--   We are borrowing a some code from generic-sop
--   ( https://hackage.haskell.org/package/generics-sop-0.3.2.0/docs/src/Generics-SOP-TH.html )
--
module Generics.MRSOP.TH
  ( deriveFamilyWith
  , deriveFamilyWithTy
  , deriveFamily
  , genFamilyDebug
  ) where

import Data.Function (on)
import Data.Char (ord , isAlphaNum)
import Data.List (sortBy, foldl')

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity

import Language.Haskell.TH hiding (match)
import Language.Haskell.TH.Syntax (liftString)

import Generics.MRSOP.Util
import Generics.MRSOP.Opaque
import Generics.MRSOP.Base.Class
import Generics.MRSOP.Base.NS
import Generics.MRSOP.Base.NP
import Generics.MRSOP.Base.Universe hiding (match)
import qualified Generics.MRSOP.Base.Metadata as Meta

import qualified Data.Map as M

data OpaqueData = OpaqueData
  { opaqueName   :: Name
  -- | Map assigning a Haskell type to its corresponding promoted
  --   Kon
  , opaqueTable  :: M.Map Name Name
  -- | Map assigning a promoted Kon to the constructor it uses
  , opaqueCons   :: M.Map Name Name
  } deriving (Eq , Show)

-- |Given the name of the first element in the family,
--  derives:
--
--    1. The other types in the family and Konstant types one needs.
--    2. the SOP code for each of the datatypes involved
--    3. One 'Element' instance per datatype
--    4. Metadada information for each of the datatypes involved
--    5. Uses the opaque-type universe provided.
deriveFamilyWith :: Name -> Q Type -> Q [Dec]
deriveFamilyWith opqName t
  = do sty              <- t >>= convertType 
       opqData          <- reifyOpaqueType opqName
       (_ , (Idxs _ m)) <- runIdxsM (reifySTy opqData sty)
       -- Now we make sure we have processed all
       -- types
       m' <- mapM extractDTI (M.toList m)
       let final = sortBy (compare `on` second) m' 
       dbg <- genFamilyDebug sty final
       res <- genFamily opqData sty final 
       return (dbg ++ res)
  where
    second (_ , x , _) = x
    
    extractDTI (sty , (ix , Nothing))
      = fail $ "Type " ++ show sty ++ " has no datatype information."
    extractDTI (sty , (ix , Just dti))
      = return (sty , ix , dti)

deriveFamilyWithTy :: Q Type -> Q Type -> Q [Dec]
deriveFamilyWithTy opq ty
  = do opqTy <- opq
       case opqTy of
         ConT opqName -> deriveFamilyWith opqName ty
         _            -> fail $ "Type " ++ show opqTy ++ " must be a name!"

deriveFamily :: Q Type -> Q [Dec]
deriveFamily = deriveFamilyWith (mkName "Singl")


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
  | Infix  ConName Fixity ty ty
  | Record ConName [ (FieldName , ty) ]
  deriving (Eq , Show , Functor)

-- ** Monadic Maps

ciMapM :: (Monad m) => (ty -> m tw) -> CI ty -> m (CI tw)
ciMapM f (Normal name tys)  = Normal name  <$> mapM f tys
ciMapM f (Infix name x l r) = Infix name x <$> f l <*> f r
ciMapM f (Record name tys)  = Record name  <$> mapM (rstr . (id *** f)) tys
  where
    rstr (a , b) = b >>= return . (a,)

dtiMapM :: (Monad m) => (ty -> m tw) -> DTI ty -> m (DTI tw)
dtiMapM f (ADT name args ci) = ADT name args <$> mapM (ciMapM f) ci
dtiMapM f (New name args ci) = New name args <$> ciMapM f ci

dtiName :: DTI ty -> DataName
dtiName (ADT name _ _) = name
dtiName (New name _ _) = name

dti2ci :: DTI ty -> [CI ty]
dti2ci (ADT _ _ cis) = cis
dti2ci (New _ _ ci)  = [ ci ]

ci2ty :: CI ty -> [ty]
ci2ty (Normal _ tys)  = tys
ci2ty (Infix _ _ a b) = [a , b]
ci2ty (Record _ tys)  = map snd tys

ciName :: CI ty -> Name
ciName (Normal n _)    = n
ciName (Infix n _ _ _) = n
ciName (Record n _)    = n

ci2Pat :: CI ty -> Q ([Name] , Pat)
ci2Pat ci
  = do ns <- mapM (const (newName "x")) (ci2ty ci)
       return (ns , (ConP (ciName ci) (map VarP ns)))

ci2Exp :: CI ty -> Q ([Name], Exp)
ci2Exp ci
  = do ns <- mapM (const (newName "y")) (ci2ty ci)
       return (ns , foldl (\e n -> AppE e (VarE n)) (ConE (ciName ci)) ns)

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
convertType (TupleT n)  = return (ConST (mkName $ '(':replicate (n-1) ',' ++ ")"))
convertType t           = fail ("convertType: Unsupported Type: " ++ show t)

trevnocType :: STy -> Type
trevnocType (AppST a b) = AppT (trevnocType a) (trevnocType b)
trevnocType (VarST n)   = VarT n
trevnocType (ConST n)
  | n == mkName "[]" = ListT
  | isTupleN n       = TupleT $ length (show n) - 1
  | otherwise        = ConT n
  where isTupleN n = take 2 (show n) == "(,"

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
       let fixity = maybe defaultFixity id $ info
       Infix name fixity <$> convertType (snd l) <*> convertType (snd r)
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

ikElim :: (Int -> a) -> (Name -> a) -> IK -> a
ikElim i k (AtomI n) = i n
ikElim i k (AtomK n) = k n

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

-- |Given an opaque type name, return the name of the constructors
--  that wrap which Haskell types.
--
--  This provides a way to customize what the generation engine
--  sees as opaque types.
--
--  For instance, suppose,
--
--  > data MySingl :: * -> * where
--  >   MyInt  :: Int  -> MySingl KInt
--  >   MyBool :: Bool -> MySingl KBool
--
--  Then,
--
--  > reifyOpaqueType ''MySingl
--  >  = M.fromList [(''Int , "KInt") , (''Bool, "KBool")]
--  >  , M.fromList [("KInt" , "MyInt") , ("KBool" , "MyBool")]
--
reifyOpaqueType :: Name -> Q OpaqueData
reifyOpaqueType opq
  = do triples <- (extract <.> reifyDec) opq
       let (hsTyMap , consMap) = genMaps triples
       return $ OpaqueData opq hsTyMap consMap
  where
    genMaps :: [(Name , Name , Name)] -> (M.Map Name Name , M.Map Name Name)
    genMaps xys = (M.fromList (map (\(x , y , _) -> (x , y)) xys)
                 ,M.fromList (map (\(_ , x , y) -> (x , y)) xys))
    
    extract :: Dec -> Q [(Name , Name , Name)]
    extract (DataD _ _ _ _ cs _) = mapM extractCon cs
    extract _
      = failMsg

    extractCon :: Con -> Q (Name , Name , Name)
    extractCon (GadtC [opqC] [(_ , ConT hsTy)] (AppT _ (PromotedT ty)))
      = return (hsTy , ty , opqC)
    extractCon _
      = failMsg

    failMsg = fail $ "The opaque-type universe you provided is of the wrong form;"
                  ++ "Check documentation for Generics.MRSOP.TH.reifyOpaqueType"

-- |Performs step 2 of the sketch;
reifySTy :: OpaqueData -> STy -> M ()
reifySTy opq sty
  = do ix <- indexOf sty
       uncurry go (styFlatten sty)
  where
    go :: STy -> [STy] -> M ()
    go (ConST name) args
      = do dec <- lift (reifyDec name >>= decInfo)
           -- TODO: Check that the precondition holds.
           let res = dtiReduce dec args
           (final , todo) <- runWriterT $ dtiMapM (convertSTy (opaqueTable opq)) res
           register sty final
           mapM_ (reifySTy opq) todo
    
    -- Convert the STy's in the fields of the constructors;
    -- tells a list of STy's we still need to process.
    convertSTy :: M.Map Name Name -> STy -> WriterT [STy] M IK
    convertSTy opqTable ty
      -- We remove sty from the list of todos
      -- otherwise we get an infinite loop
      | ty == sty = AtomI <$> lift (indexOf ty)
      | isClosed ty
      = case makeCons opqTable ty of
          Just k  -> return (AtomK k)
          Nothing -> do ix     <- lift (indexOf ty)
                        hasDti <- lift (hasData ty)
                        when (not hasDti) (tell [ty])
                        return (AtomI ix)
      | otherwise
      = fail $ "I can't convert type variable " ++ show ty
              ++ " when converting " ++ show sty

    makeCons :: M.Map Name Name -> STy -> Maybe Name
    makeCons opqTable (ConST n) = M.lookup n opqTable
    makeCons opqTable _         = Nothing

-----------------------------
-- * Generating the Code * --
-----------------------------

-- Code generation happens in a few separate parts.
-- Given a datatype:
-- 
-- > data R a = a :>: [R a]
-- >          | Leaf a
-- >          deriving Show
--
-- We need to generate:
--
-- 1. The Family and the codes
-- 1.1 > type FamRose   = '[ [R Int] , R Int ]
-- 1.2 > type D0_ = Z
--     > type D1_ = S Z
-- 1.3 > type CodesRose = '[ '[ '[] , '[I D1_ , I D0_] ]
--     >                   , '[ '[K KInt , I D0_] , '[K KInt] ]
--     >                   ]
--
-- 2. The index of each type in the family.
-- 2.1 types
-- > pattern IdxRInt     = SZ
-- > pattern IdxListInt  = SS SZ
--
-- 2.1.1 Here-There Synonyms
-- > pattern HT0_ d = Here d
-- > pattern HT1_ d = There (Here d)
--
--  TODO:
--   This has an issue; if we import two modules with code generation
--   the HT0, HT1, ... HTn names will clash.
--   Same with D0_, D1_, Dn_ in part (1.2) above.
--   These were an effort in circumventing the GHC memory leak,
--   but since it does not solve the problem, we should consider
--   dropping that.
--
-- 2.2. constructors
-- > pattern a :>:_ as = Tag CZ      (NA_K a :* NA_I (El as) :* NP0)
-- > pattern Leaf_ a   = Tag (CS CZ) (NA_K a :* NP0)
-- > pattern nil_      = Tag CZ NP0
-- > pattern a :_ as   = Tag (CS CZ) (NA_I a :* NA_I (El as) :* NP0)
--
-- 3. The instance:
-- > instance Family Singl FamRose CodesRose where
--
-- 3.1. for each type in (1)
-- >   sfrom' (SS SZ) (El (a :>: as))
-- >     = Rep $ HT0_ (NA_K (SInt a) :* NA_I (El as) :* NP0)
-- >   sfrom' (SS SZ) (El (Leaf a))
-- >     = Rep $ HT1_ (NA_K (SInt a) :* NP0)
-- >   sfrom' SZ (El [])
-- >     = Rep $ HT0_ NP0
-- >   sfrom' SZ (El (x:xs))
-- >     = Rep $ HT1_ (NA_I (El x) :* NA_I (El xs) :* NP0)
--
-- 3.2.
-- > 
-- >   sto' SZ (Rep (HT0_ NP0))
-- >     = El []
-- >   sto' SZ (Rep (HT1_ (NA_I (El x) :* NA_I (El xs) :* NP0)))
-- >     = El (x : xs)
-- >   sto' (SS SZ) (Rep (HT0_ (NA_K (SInt a) :* NA_I (El as) :* NP0)))
-- >     = El (a :>: as)
-- >   sto' (SS SZ) (Rep (HT1_ (NA_K (SInt a) :* NP0)))
-- >     = El (Leaf a)
--
-- 4. Metadata for each type in (1)
-- > instance HasDatatypeInfo Singl FamRose CodesRose where
-- >   datatypeInfo Proxy CZ = ...
-- >   datatypeInfo Proxy (CS CZ) = ... 

-- |The input data for the generation is an ordered list
--  (on the second component of the tuple) of STy's and
--  their datatype info.
type Input = [(STy , Int , DTI IK)]

-- Generates a type-level list of 'a's
tlListOf :: (a -> Type) -> [a] -> Type
tlListOf f = foldr (\h r -> AppT (AppT PromotedConsT (f h)) r) PromotedNilT

-- generate a type-level Nat
int2Type :: Int -> Type
int2Type 0 = tyZ
int2Type n = AppT tyS (int2Type (n - 1))

-- generate the name of the type synonym corresponding to
-- this int.
int2TySynName :: Int -> Name
int2TySynName i = mkName $ "D" ++ show i ++ "_"

-- generates a Snat for the given Int
int2SNatPat :: Int -> Pat
int2SNatPat 0 = ConP (mkName "SZ") []
int2SNatPat n = ConP (mkName "SS") [int2SNatPat $ n-1]

-- Our promoted type constructors
tyS = PromotedT (mkName "S")
tyZ = PromotedT (mkName "Z")
tyI = PromotedT (mkName "I")
tyK = PromotedT (mkName "K")

-- Generate rhs of piece (1.3)
inputToCodes :: Input -> Q Type
inputToCodes = return . tlListOf dti2Codes . map third
  where
    third (_ , _ , x) = x

dti2Codes :: DTI IK -> Type
dti2Codes = tlListOf ci2Codes . dti2ci

ci2Codes :: CI IK -> Type
ci2Codes = tlListOf ik2Codes . ci2ty

ik2Codes :: IK -> Type
-- VCM: int pattern synonyms make too many name clashes
--      if we mix up modules.
ik2Codes (AtomI n) = AppT tyI $ int2Type n -- ConT (int2TySynName n)
ik2Codes (AtomK k) = AppT tyK $ PromotedT k

{-
  VCM: GHC performance HACK

-- Generates piece (1.2); we do so by
-- finding what's the maximum type index used
-- in all DatatypeInformation we have and then generate
-- all type synonyms up to it.
inputToTySynNums :: Input -> Q [Dec]
inputToTySynNums input
  = let maxI = maximum $ map (localMax . third) input
     in return $ map genTySynNum [0..maxI]
  where
    third (_ , _ , x) = x

    localMax :: DTI IK -> Int
    localMax = foldr (\ci aux -> aux `max` getMaxIdx (ci2ty ci)) 0 . dti2ci

    getMaxIdx :: [IK] -> Int
    getMaxIdx = foldr (ikElim max (const id)) 0

    genTySynNum i = TySynD (int2TySynName i) [] (int2Type i)
-}

-- generates rhs of piece (1.1)
inputToFam :: Input -> Q Type
inputToFam = return . tlListOf trevnocType . map first
  where
    first (x , _ , _) = x

-- | @styToName "List (R Int)" == "ListRInt"@
styToName :: STy -> Name
styToName = mkName . styFold (++) nameBase (fixList . nameBase)
  where
    -- VCM: ugly hack; but list is a reserved name.
    --      The hack is needed either here or in reify.
    fixList :: String -> String
    fixList n
      | n == "[]"        = "List"
      | take 2 n == "(," = "Tup" ++ show (length n - 2) 
      | otherwise        = n

onBaseName :: (String -> String) -> Name -> Name
onBaseName f = mkName . f . nameBase

codesName :: STy -> Q Name
codesName = return . onBaseName ("Codes" ++) . styToName

familyName :: STy -> Q Name
familyName = return . onBaseName ("Fam" ++) . styToName

genPiece1 :: STy -> Input -> Q [Dec]
genPiece1 first ls
  = do -- nums  <- inputToTySynNums ls -- TODO: Remove this hack
       codes <- TySynD <$> codesName first
                       <*> return []
                       <*> inputToCodes ls
       fam   <- TySynD <$> familyName first
                       <*> return []
                       <*> inputToFam ls
       return [fam , codes] -- (nums ++ [fam , codes])

idxPatSynName :: STy -> Name
idxPatSynName = styToName . (AppST (ConST (mkName "Idx")))
       
idxPatSyn :: STy -> Pat
idxPatSyn = flip ConP [] . idxPatSynName

{-
  VCM: HACK

-- |@htPatSynName ci@ will generate the
--  pattern synonym name for constructor ci.
--
--  Since all our patterns are supposed to be @PrefixPatSyn@s,
--  we need to translate the infix names to something
--  Haskell will accept.
htPatSynName :: Int -> CI IK -> Name
htPatSynName dtiIx ci = mkName . translate . nameBase . ciName $ ci
  where
    translate = ("Pat" ++) . foldl' (\str l -> str ++ tr l ) (show dtiIx)
    tr l | isAlphaNum l = l:[]
         | otherwise    = show $ ord l

htPatSynExp :: Int -> CI IK -> Q Exp
htPatSynExp dtiIx = return . ConE . htPatSynName dtiIx

-}
{-
  We tried this in order to help the exhaustiveness checker in GHC.
  I'm removing this hack to avoid name clashes. Our experiments
  showed that this did not help at all.

genHereTherePatSyn :: OpaqueData -> STy -> Input -> Q [Dec]
genHereTherePatSyn opq first ls
  = flat . concat <$> mapM (\(_ , ix , dti) -> genHereThereFor ix dti) ls
  where
    flat             = foldl' (\ac (x , y) -> x:y:ac) []
    third (_ , _, x) = x

    famName = ConT <$> familyName first

    inj :: Int -> Q Pat -> Q Pat
    inj 0 p = [p| Here $p                  |]
    inj n p = [p| There ( $(inj (n-1) p) ) |]

    -- Returns one pattern synonym for each constructor in
    -- the datatype and a type signature for it.
    genHereThereFor :: Int -> DTI IK -> Q [(Dec , Dec)]
    genHereThereFor dtiIx dti
      = do let dtiCode = dti2Codes dti
           let cisIx   = zip [0..] (dti2ci dti)
           forM cisIx $ \ (ix , ci)
             -> (,) <$> genHT_decl dtiCode dtiIx ix ci
                    <*> genHT_def          dtiIx ix ci

    opqName = return (ConT $ opaqueName opq)

    genHT_decl dtiCode dtiIx ix ci
      = PatSynSigD (htPatSynName dtiIx ci)
          <$> [t| PoA $opqName (El $famName) $(return $ ci2Codes ci)
                -> NS (PoA $opqName (El $famName)) $(return dtiCode) |]

    genHT_def dtiIx ix ci
      = do var <- newName "d"
           PatSynD (htPatSynName dtiIx ci) (PrefixPatSyn [var]) ImplBidir
             <$> inj ix (return $ VarP var)
-}

genIdxPatSyn :: STy -> Int -> Q Dec
genIdxPatSyn sty ix
  = return (PatSynD (idxPatSynName sty) (PrefixPatSyn []) ImplBidir (int2SNatPat ix))

-- |Generating pattern synonyms for the type indexes
--  and the pattern synonyms for the constructors.
--
--  > pattern IdxRInt = SZ
--  > pattern IdxListRInt = SS SZ
--
genPiece2 :: OpaqueData -> STy -> Input -> Q [Dec]
genPiece2 opq first ls
  = do p21  <- mapM (\(sty , ix , dti) -> genIdxPatSyn sty ix) ls
       p22  <- genPiece2_2 opq first ls
       -- p211 <- genHereTherePatSyn opq first ls
       return $ p21 ++ p22

-- |Generating pattern synonyms for constructors with 'Tag'
--
--  This is trickier than it looks at first sight.
--  If we have occurences of @Maybe A@ and @Maybe B@ in our
--  mutually recursive family, we have to generate two sets of
--  @Just@s and @Nothing@s, otherwise we will have a name clash.
--
--  Infix constructors also receive special treatment.
--  suppose @(:*:)@ is the 4th constructor of a type @Op x@,
--  The pattern syn for an instantiation of @x@ to @Int@, @Op Int@,
--  will be named @OpInt_Ifx4@.
--
genPiece2_2 :: OpaqueData -> STy -> Input -> Q [Dec]
genPiece2_2 opq first ls
  = concat <$> mapM (\(sty , ix , dti) -> genTagPatSyns sty ix dti) ls
  where
    genTagPatSyns :: STy -> Int -> DTI IK -> Q [Dec]
    genTagPatSyns sty ix dti
      = concat <$> mapM (uncurry $ genTagPatSynFor ix sty)
                        (zip [0..] $ dti2ci dti)

    genTagPatSynFor :: Int -> STy -> Int -> CI IK -> Q [Dec]
    genTagPatSynFor ix sty cidx ci
      = let fields = ci2ty ci
         in do vars <- mapM (const (newName "p")) fields
               let namedFields = zip fields vars
               name <- patSynName sty cidx ci
               pat <- [p| Tag $(int2Constr cidx) $(tagPatSynProd namedFields) |]
               let pDef = PatSynD name (PrefixPatSyn vars) ImplBidir pat
               phiN <- newName "phi"
               konN <- newName "kon"
               patTy <- genTagPatType ix phiN konN fields
               let pTy = PatSynSigD name patTy
               return [pTy , pDef]

    genTagPatType :: Int -> Name -> Name -> [IK] -> Q Type
    genTagPatType tyIx phi kon (AtomK konst : rest)
      = [t| $(return $ VarT kon) $(return (ConT konst))
            -> $(genTagPatType tyIx phi kon rest) |] 
    genTagPatType tyIx phi kon (AtomI ni : rest)
      = [t| $(return (VarT phi)) $(return $ int2Type ni)
            -> $(genTagPatType tyIx phi kon rest) |]
    genTagPatType tyIx phi kon []
      = [t| View $(return $ VarT kon)
                 $(return $ VarT phi)
                 (Lkup $(return $ int2Type tyIx)
                       $(ConT <$> codesName first))
        |]

    patSynName :: STy -> Int -> CI IK -> Q Name
    patSynName sty cidx ci
      | ciHasIllegalName ci
      = let styname = nameBase $ styToName sty
         in return . mkName $ styname ++ "_Ifx" ++ show cidx
    -- This is a constructor of a type that is not applied
    -- to any argument; hence there is no risk of name clashing.
      | ConST _ <- sty
      = return . mkName $ nameBase (ciName ci) ++ "_"
    -- Here we will preffix the the constructor name with the
    -- type it belongs to.
      | otherwise
      = let styname = nameBase $ styToName sty
         in return . mkName $ styname ++ nameBase (ciName ci) ++ "_"

    ciHasIllegalName :: CI ty -> Bool
    ciHasIllegalName (Infix _ _ _ _) = True
    ciHasIllegalName ci = any (not . isAlphaNum) $ nameBase (ciName ci)

    tagPatSynProd :: [(IK , Name)] -> Q Pat
    tagPatSynProd []     = [p| NP0 |]
    tagPatSynProd (h:hs) = [p| $(tagPatSynProdHead h) :* ( $(tagPatSynProd hs) ) |]

    int2Constr :: Int -> Q Pat
    int2Constr 0 = [p| CZ |]
    int2Constr n = [p| CS $(int2Constr (n-1)) |]

    tagPatSynProdHead :: (IK , Name) -> Q Pat
    tagPatSynProdHead (AtomI _ , name) = [p| NA_I $(return . VarP $ name) |]
    tagPatSynProdHead (AtomK _ , name) = [p| NA_K $(return . VarP $ name) |]

genPiece3 :: OpaqueData -> STy -> Input -> Q Dec
genPiece3 opq first ls
  = head <$> [d| instance Family $(return $ ConT $ opaqueName opq)
                                 $(ConT <$> familyName first)
                                 $(ConT <$> codesName first)
                   where sfrom' = $(genPiece3_1 opq ls)
                         sto'   = $(genPiece3_2 opq ls) |]

-- |Given a datatype information, generates a pattern
--  and an expression from it. The int here
--  indicates the number of the constructor.
--
--  > ci2PatExp opq IdxBinTree 3 (Normal "Bin" [VarT a , VarT a])
--  >   = ( El (Bin x_1 x_2)
--  >     , Rep (There (There (Here (NA_I (El x_1) :* NA_I (El x_2) :* NP0))))
--  >     )
ci2PatExp :: OpaqueData -> Int -> Int -> CI IK -> Q (Pat , Exp)
ci2PatExp opq dtiIx cIdx ci
  = do (vars , pat) <- ci2Pat ci
       bdy          <- [e| Rep $(inj cIdx $ genBdy (zip vars (ci2ty ci))) |]
       return (ConP (mkName "El") [pat] , bdy)
  where
    inj :: Int -> Q Exp -> Q Exp
    inj 0 e = [e| Here $e              |]
    inj n e = [e| There $(inj (n-1) e) |]

    genBdy :: [(Name , IK)] -> Q Exp
    genBdy []       = [e| NP0 |]
    genBdy (x : xs) = [e| $(mkHead x) :* ( $(genBdy xs) ) |]


    mkHead (x , AtomI _) = [e| NA_I (El $(return (VarE x))) |]
    mkHead (x , AtomK k) = [e| NA_K $(makeK opq k (\r -> AppE (ConE r) (VarE x))) |]
    -- mkHead (x , AtomK k) = [e| NA_K $(return (AppE (ConE (mkK k)) (VarE x))) |]

-- | Just like 'ci2PatExp', but the other way around.
--
--  > ci2ExpPat opq IdxBinTree 2 (Normal "Bin" [VarT a , VarT a])
--  >   = ( Rep (There (There (Here (NA_I (El x_1) :* NA_I (El x_2) :* NP0))))
--        , El (Bin x_1 x_2)
--  >     )
ci2ExpPat :: OpaqueData -> Int -> Int -> CI IK -> Q (Pat , Exp)
ci2ExpPat opq dtiIx cIdx ci 
  = do (vars , exp) <- ci2Exp ci
       pat          <- [p| Rep $(inj cIdx $ genBdy (zip vars (ci2ty ci))) |]
       return (pat , AppE (ConE $ mkName "El") exp)
  where
    inj :: Int -> Q Pat -> Q Pat
    inj 0 e = [p| Here $e              |]
    inj n e = [p| There $(inj (n-1) e) |]
    
    genBdy :: [(Name , IK)] -> Q Pat
    genBdy []       = [p| NP0 |]
    genBdy (x : xs) = [p| $(mkHead x) :* ( $(genBdy xs) ) |]


    mkHead (x , AtomI _) = [p| NA_I (El $(return (VarP x))) |]
    mkHead (x , AtomK k) = [p| NA_K $(makeK opq k (flip ConP [VarP x])) |]
    -- mkHead (x , AtomK k) = [p| NA_K $(return (ConP (mkK k) [VarP x])) |]


makeK :: OpaqueData -> Name -> (Name -> a) -> Q a
makeK opq n cont
  = case M.lookup n (opaqueCons opq) of
      Nothing -> fail $  "makeK: Can't find constructor for " ++ show n ++ " in opaque def"
      Just c  -> return $ cont c


match :: Pat -> Exp -> Match
match pat bdy = Match pat (NormalB bdy) []

-- Adds a matchall clause; for instance:
--
-- > matchAll [Just x -> 1] = [Just x -> 1 , _ -> error "matchAll"]
--
matchAll :: [Match] -> [Match]
matchAll = (++ [match WildP err])
  where
    err = AppE (VarE (mkName "error")) (LitE (StringL "matchAll"))

genPiece3_1 :: OpaqueData -> Input -> Q Exp
genPiece3_1 opq input
  = LamCaseE <$> mapM (\(sty , ix , dti) -> clauseForIx sty ix dti) input
  where
    clauseForIx :: STy -> Int -> DTI IK -> Q Match
    clauseForIx sty ix dti = match (idxPatSyn sty)
                       <$> (LamCaseE <$> genMatchFor ix dti)
    
    genMatchFor :: Int -> DTI IK -> Q [Match]
    genMatchFor ix dti = map (uncurry match) <$> mapM (uncurry $ ci2PatExp opq ix)
                                                      (zip [0..] $ dti2ci dti)
      
genPiece3_2 :: OpaqueData -> Input -> Q Exp
genPiece3_2 opq input
  = LamCaseE . matchAll <$> mapM (\(sty , ix , dti) -> clauseForIx sty ix dti) input
  where    
    clauseForIx :: STy -> Int -> DTI IK -> Q Match
    clauseForIx sty ix dti = match (idxPatSyn sty)
                       <$> (LamCaseE . matchAll <$> genMatchFor ix dti)
      
    genMatchFor :: Int -> DTI IK -> Q [Match]
    genMatchFor ix dti = map (uncurry match) <$> mapM (uncurry $ ci2ExpPat opq ix)
                                                      (zip [0..] $ dti2ci dti)

genPiece4 :: OpaqueData -> STy -> Input -> Q [Dec]
genPiece4 opq first ls
  = [d| instance Meta.HasDatatypeInfo $opqName
                                      $(ConT <$> familyName first)
                                      $(ConT <$> codesName first)
          where datatypeInfo _ = $(genDatatypeInfoClauses ls) |]
  where
    opqName = return (ConT $ opaqueName opq)

    genDatatypeInfoClauses :: Input -> Q Exp
    genDatatypeInfoClauses input
      = LamCaseE <$> mapM genDatatypeInfoMatch input
    
    genDatatypeInfoMatch :: (STy , Int , DTI IK) -> Q Match
    genDatatypeInfoMatch (sty , idx , dti)
      = match (int2SNatPat idx) <$> genInfo sty dti 

    genMod :: Name -> Q Exp
    genMod = strlit . maybe "" id . nameModule

    strlit :: String -> Q Exp
    strlit = return . LitE . StringL

    genDatatypeName :: STy -> Q Exp
    genDatatypeName = styFold (\e1 e2 -> [e| ( $e1 Meta.:@: $e2 ) |])
                              (\n -> [e| Meta.Name $(strlit (nameBase n)) |] )
                              (\n -> [e| Meta.Name $(strlit (nameBase n)) |] )

    genInfo :: STy -> DTI IK -> Q Exp
    genInfo sty (ADT name _ cis)
      = [e| Meta.ADT $(genMod name) $(genDatatypeName sty) $(genConInfoNP cis) |]
    genInfo sty (New name _ ci)
      = [e| Meta.New $(genMod name) $(genDatatypeName sty) $(genConInfo ci) |]

    genConInfo :: CI IK -> Q Exp
    genConInfo (Record conname fields)
      = [e| Meta.Record $(strlit $ nameBase conname) $(genFieldInfo $ map fst fields) |]
    genConInfo (Normal conname _)
      = [e| Meta.Constructor $(strlit $ nameBase conname) |]
    genConInfo (Infix conname fix _ _)
      = [e| Meta.Infix $(strlit $ nameBase conname) $(genAssoc fix) $(genFix fix) |]
      where
        genAssoc (Fixity _ InfixL) = [e| Meta.LeftAssociative  |]
        genAssoc (Fixity _ InfixR) = [e| Meta.RightAssociative |]
        genAssoc (Fixity _ InfixN) = [e| Meta.NotAssociative   |]

        genFix (Fixity i _) = return . LitE . IntegerL . fromIntegral $ i

    genFieldInfo :: [ FieldName ] -> Q Exp
    genFieldInfo []     = [e| NP0 |]
    genFieldInfo (f:fs) = [e| Meta.FieldInfo $(strlit . nameBase $ f) :* ( $(genFieldInfo fs) ) |]

    genConInfoNP :: [ CI IK ] -> Q Exp
    genConInfoNP []       = [e| NP0 |]
    genConInfoNP (ci:cis) = [e| $(genConInfo ci) :* ( $(genConInfoNP cis) ) |]

-- |@genFamily opq init fam@ generates a type-level list
--  of the codes for the family. It also generates
--  the necessary 'Element' instances.
--
--  Precondition, input is sorted on second component.
genFamily :: OpaqueData -> STy -> Input -> Q [Dec]
genFamily opq first ls
  = do p1 <- genPiece1 first ls
       p2 <- genPiece2 opq first ls
       p3 <- genPiece3 opq first ls
       p4 <- genPiece4 opq first ls
       return $ p1 ++ p2 ++ [p3] ++ p4

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
