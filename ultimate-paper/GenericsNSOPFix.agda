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

module GenericsNSOPFix where

  -- Start defining our kinds!
  infixr 50 _⇒_
  data 𝕂 : Set where
    ⋆   : 𝕂
    _⇒_ : 𝕂 → 𝕂 → 𝕂

  -- We now map these to Set₁
  ⟦_⟧K : 𝕂 → Set₁
  ⟦ ⋆       ⟧K = Set
  ⟦ k₁ ⇒ k₂ ⟧K = ⟦ k₁ ⟧K → ⟦ k₂ ⟧K

  -- How many positions does a kind have?
  -- Analogous to Pos in the haskell code.
  arity : 𝕂 → ℕ
  arity ⋆         = 0
  arity (k₁ ⇒ k₂) = 1 + arity k₂

  -- Positions in a kind
  pos𝕂 : 𝕂 → Set
  pos𝕂 k = Fin (arity k)

  -- Gets the kind on the n'th position
  arg : (k : 𝕂) → pos𝕂 k → 𝕂
  arg ⋆ ()
  arg (k₁ ⇒ k₂) zero    = k₁
  arg (k₁ ⇒ k₂) (suc n) = arg k₂ n

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
    Var : (n : pos𝕂 k) → Term k (arg k n)
    Rec : Term k k
    Kon : ∀{k₁}    → ⟦ k₁ ⟧K → Term k k₁
    App : ∀{k₁ k₂} → Term k (k₁ ⇒ k₂) → Term k k₁ →  Term k k₂
    
  -- This is called LoT in Haskell
  data Γ : 𝕂 → Set₁ where
    []  : Γ ⋆
    _∷_ : ∀{k₁ k₂} → ⟦ k₁ ⟧K → Γ k₂ → Γ (k₁ ⇒ k₂)

  -- looks an argument up in a context
  lkup : ∀{k} → Γ k → (n : pos𝕂 k) → ⟦ arg k n ⟧K
  lkup []       ()
  lkup (t ∷ ts) zero    = t
  lkup (t ∷ ts) (suc n) = lkup ts n

  Ty : ∀{res k} → ⟦ k ⟧K → Γ k → Term k res → ⟦ res ⟧K
  Ty vk γ (Var n) = lkup γ n
  Ty vk γ Rec     = vk
  Ty vk γ (Kon x) = x
  Ty vk γ (App f x) = Ty vk γ f (Ty vk γ x)

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

  ⟦_⟧A : ∀{k} → Field k → ⟦ k ⟧K → Γ k → Set₁
  ⟦ Explicit t   ⟧A vk γ = Lift (Ty vk γ t)
  ⟦ Implicit ctr ⟧A vk γ = ctr γ
  
  ⟦_⟧P : ∀{k} → Prod k → ⟦ k ⟧K → Γ k → Set₂
  ⟦ as ⟧P vk γ = All (λ α → ⟦ α ⟧A vk γ) as

  ⟦_⟧S : ∀{k} → SoP k → ⟦ k ⟧K → Γ k → Set₂
  ⟦ ps ⟧S vk γ = Any (λ π → ⟦ π ⟧P vk γ) ps

  app : ∀{k}(T : ⟦ k ⟧K) → Γ k → Set
  app {⋆}       T [] = T
  app {k₁ ⇒ k₂} T (x ∷ γ) = app (T x) γ

  record G {k}(T : ⟦ k ⟧K) : Set₂ where
    field
      Code : SoP k
      from : (γ : Γ k) → app T γ → ⟦ Code ⟧S T γ


  {-# NON_TERMINATING #-}
  Fix : ∀{k}(σ : SoP k)(γ : Γ k) → Set₂
  Fix σ γ = ⟦ σ ⟧S {!!} {!!}
{-
  data Fix {k}(σ : SoP k)(γ : Γ k) : ⟦ k ⟧K where
    fix : ⟦ σ ⟧S (Fix σ γ) γ → Fix σ γ
-}
{-
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
  maybe = [] ∷ (Explicit (Var Fin.zero) ∷ []) ∷ []

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
  sopX = (Implicit ctr ∷ Explicit (Var Fin.zero) ∷ []) ∷ []
    where
      ctr : (γ : Γ (⋆ ⇒ ⋆)) → Set₁
      ctr (x ∷ []) = x ≡ Bool
  
  xbool : Bool → ⟦ sopX ⟧S (Bool ∷ [])
  xbool b = here (refl ∷ ((lift b) ∷ []))
   
-}
{-

  gfmap : {t : SoP (⋆ ⇒ ⋆)}{A B : Set}
        → (A → B)
        → ⟦ t ⟧S (A ∷ []) → ⟦ t ⟧S (B ∷ [])
  gfmap = {!!}
-}
