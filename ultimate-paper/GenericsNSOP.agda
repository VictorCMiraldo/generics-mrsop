open import Level

open import Data.Empty
open import Data.Product renaming (map to <_,_>)
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Unit.NonEta

open import Data.Fin 
  hiding (_+_; lift)

open import Data.Nat hiding (_⊔_)
open import Data.Bool

open import Relation.Binary.PropositionalEquality

module GenericsNSOP where

  -- Start defining our kinds!
  infixr 50 _⇒_
  data 𝕂 : Set where
    ⋆   : 𝕂
    _⇒_ : 𝕂 → 𝕂 → 𝕂

  -- We now map these to Set₁
  ⟦_⟧K : 𝕂 → Set₁
  ⟦ ⋆       ⟧K = Set
  ⟦ k₁ ⇒ k₂ ⟧K = ⟦ k₁ ⟧K → ⟦ k₂ ⟧K

  data TyVar : 𝕂 → 𝕂 → Set where
    VZ : ∀{k    ks}              → TyVar (k  ⇒ ks) k
    VS : ∀{k' k ks} → TyVar ks k → TyVar (k' ⇒ ks) k

  -- Finally, our term language. 
  -- Imagine we have something like:
  --
  -- data T (a :: * -> *) (b :: *) (c :: * -> *)
  --
  -- The 'context', or, kind of T is (* -> *) -> * -> (* -> *) -> * 
  -- call it kt. An example of inhabitants of Term kt ⋆
  -- could be:
  --
  --    Var 2 ; App (Var 0) (Kon ℕ) ; ...
  --
  -- We just have the applicative fragment of the simply typed
  -- lambda calculus here.
  data Term (k : 𝕂) : 𝕂 → Set₁ where
    Var : ∀{k₁}    → TyVar k k₁ → Term k k₁
    Kon : ∀{k₁}    → ⟦ k₁ ⟧K → Term k k₁
    App : ∀{k₁ k₂} → Term k (k₁ ⇒ k₂) → Term k k₁ →  Term k k₂
    
  -- This is called LoT in Haskell
  data Γ : 𝕂 → Set₁ where
    []  : Γ ⋆
    _∷_ : ∀{k₁ k₂} → ⟦ k₁ ⟧K → Γ k₂ → Γ (k₁ ⇒ k₂)

  Ty : ∀{res k} → Γ k → Term k res → ⟦ res ⟧K
  Ty []       (Var ())
  Ty (γ ∷ γs) (Var VZ)     = γ
  Ty (γ ∷ γs) (Var (VS n)) = Ty γs (Var n)
  Ty γ        (Kon x)      = x
  Ty γ        (App f x)    = Ty γ f (Ty γ x)

  -- Now, a constraint over kind k is just a map from k to set, or
  -- a predicate over it.
  Constraint : 𝕂 → 𝕂
  Constraint k = k ⇒ ⋆

  -- Here's the magic! Took me a while to figure this out!
  --
  -- An explicit field is some combination of things
  -- in scope to make up a set.
  --
  -- An implicit field (aka Constraint), is a predicate over
  -- whatever things will be in scope by the time
  -- we are interpreting codes.
  data Field (k : 𝕂) : Set₂ where
    Explicit : Term k ⋆     → Field k
    Implicit : (Γ k → Set₁) → Field k

  Prod : 𝕂 → Set₂
  Prod k = List (Field k)

  SoP : 𝕂 → Set₂
  SoP k = List (Prod k)

  ⟦_⟧A : ∀{k} → Field k → Γ k → Set₁
  ⟦ Explicit t   ⟧A γ = Lift (Ty γ t)
  ⟦ Implicit ctr ⟧A γ = ctr γ
  
  ⟦_⟧P : ∀{k} → Prod k → Γ k → Set₂
  ⟦ as ⟧P γ = All (λ α → ⟦ α ⟧A γ) as

  ⟦_⟧S : ∀{k} → SoP k → Γ k → Set₂
  ⟦ ps ⟧S γ = Any (λ π → ⟦ π ⟧P γ) ps

  app : ∀{k}(T : ⟦ k ⟧K) → Γ k → Set
  app {⋆}       T [] = T
  app {k₁ ⇒ k₂} T (x ∷ γ) = app (T x) γ

  record G {k}(T : ⟦ k ⟧K) : Set₂ where
    field
      Code : SoP k
      from : (γ : Γ k) → app T γ → ⟦ Code ⟧S γ

  -- gfmap

  -- This is trickier. We can only automatically map
  -- if a type has no constraints.
  -- We call this ADTs
  isADT-a : ∀{k} → Field k → Set₂
  isADT-a (Explicit _) = Lift Unit
  isADT-a (Implicit _) = Lift ⊥

  isADT-p : ∀{k} → Prod k → Set₂
  isADT-p = All isADT-a

  isADT : ∀{k} → SoP k → Set₂
  isADT = All isADT-p

  κ : 𝕂
  κ = ⋆ ⇒ ⋆

  getField : ∀{k}(f : Field k)(prf : isADT-a f)
           → Term k ⋆
  getField (Explicit t) _ = t
  getField (Implicit _) (lift ())

  record FunctorField (t : Term κ ⋆) : Set₁ where
    field
      gfmap : ∀{A B}(f : A → B) → Ty (A ∷ []) t → Ty (B ∷ []) t
  open FunctorField

  data Allᵢ {a b}{A : Set a}{P : A → Set a}(Q : (x : A) → P x → Set b)
          : {l : List A} → All P l → Set (a ⊔ b) where
    Nil  : Allᵢ Q []
    Cons : ∀{x xs}(px : P x){pxs : All P xs}(qx : Q x px) 
         → Allᵢ Q pxs → Allᵢ Q (px ∷ pxs)

  lift-map : ∀{a b}{A₁ A₂ : Set a}(f : A₁ → A₂)
           → Lift {a} {b} A₁ → Lift {a} {b} A₂
  lift-map f (lift x) = lift (f x)

  A-map : ∀{A B}(a : Field κ)(prf : isADT-a a)(f : A → B)
        → FunctorField (getField a prf) → ⟦ a ⟧A (A ∷ []) → ⟦ a ⟧A (B ∷ [])
  A-map (Implicit _) (lift ()) f _ _ 
  A-map (Explicit _) _         f ff x = lift-map (gfmap ff f) x
  
  P-map : ∀{A B}(p : Prod κ)(prf : isADT-p p)(f : A → B)
        → Allᵢ (λ x fx → FunctorField (getField x fx)) prf 
        → ⟦ p ⟧P (A ∷ []) → ⟦ p ⟧P (B ∷ [])
  P-map .[] prf f ffs [] = []
  P-map .(_ ∷ _) (h ∷ hs) f (Cons {x = x} _ qx r) (px ∷ xs) 
   = A-map x h f qx px ∷ P-map _ hs f r xs 

  S-map : ∀{A B}(s : SoP κ)(prf : isADT s)(f : A → B)
        → Allᵢ (λ p fp → Allᵢ (λ x fx → FunctorField (getField x fx)) fp) prf 
        → ⟦ s ⟧S (A ∷ []) → ⟦ s ⟧S (B ∷ [])
  S-map (s ∷ _) (h ∷ hs) f (Cons {x = x} _ ff ffs) (here p) 
    = here (P-map s h f ff p)
  S-map (_ ∷ s) (h ∷ hs) f (Cons {x = x} _ ff ffs) (there p) 
    = there (S-map s hs f ffs p)

  -- Maybe type:
  maybe : SoP (⋆ ⇒ ⋆)
  maybe = [] ∷ (Explicit (Var VZ) ∷ []) ∷ []

  nothing : ∀{A} → ⟦ maybe ⟧S (A ∷ [])
  nothing = here []

  just : ∀{A} → A → ⟦ maybe ⟧S (A ∷ [])
  just x = there (here (lift x ∷ []))

  -- maybe-map

  maybe-is-adt : isADT maybe
  maybe-is-adt = [] ∷ (((lift unit) ∷ []) ∷ [])

  maybe-ff : Allᵢ (λ p fp → Allᵢ (λ x fx → FunctorField (getField x fx)) fp) maybe-is-adt
  maybe-ff = Cons [] Nil 
            (Cons ((lift unit) ∷ []) 
              (Cons (lift unit) (record { gfmap = λ f x → f x }) 
                    Nil) Nil) 

  maybe-map : ∀{A B} → (f : A → B) → ⟦ maybe ⟧S (A ∷ []) → ⟦ maybe ⟧S (B ∷ [])
  maybe-map f = S-map maybe maybe-is-adt f maybe-ff

  -- One with constraints
  data X : Set → Set where
    XBool : Bool → X Bool

  sopX : SoP (⋆ ⇒ ⋆)
  sopX = (Implicit ctr ∷ Explicit (Var VZ) ∷ []) ∷ []
    where
      ctr : (γ : Γ (⋆ ⇒ ⋆)) → Set₁
      ctr (x ∷ []) = x ≡ Bool
  
  xbool : Bool → ⟦ sopX ⟧S (Bool ∷ [])
  xbool b = here (refl ∷ ((lift b) ∷ []))
   
{-

  gfmap : {t : SoP (⋆ ⇒ ⋆)}{A B : Set}
        → (A → B)
        → ⟦ t ⟧S (A ∷ []) → ⟦ t ⟧S (B ∷ [])
  gfmap = {!!}
-}
