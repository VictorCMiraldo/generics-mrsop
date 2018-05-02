open import Level

open import Data.Empty
open import Data.Product renaming (map to <_,_>)
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Unit.NonEta

open import Data.Fin 
  hiding (_+_; lift)

open import Data.Nat
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

  Ty : ∀{res k} → Γ k → Term k res → ⟦ res ⟧K
  Ty γ (Var n) = lkup γ n
  Ty γ (Kon x) = x
  Ty γ (App f x) = Ty γ f (Ty γ x)
     
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


  -- Maybe type:
  maybe : SoP (⋆ ⇒ ⋆)
  maybe = [] ∷ (Explicit (Var Fin.zero) ∷ []) ∷ []

  nothing : ∀{A} → ⟦ maybe ⟧S (A ∷ [])
  nothing = here []

  just : ∀{A} → A → ⟦ maybe ⟧S (A ∷ [])
  just x = there (here (lift x ∷ []))

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
   


  gfmap : {t : SoP (⋆ ⇒ ⋆)}{A B : Set}
        → (A → B)
        → ⟦ t ⟧S (A ∷ []) → ⟦ t ⟧S (B ∷ [])
  gfmap = {!!}
