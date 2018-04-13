open import Level

open import Data.Empty
open import Data.Product renaming (map to <_,_>)
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Unit.NonEta

open import Data.Nat
open import Data.Bool

open import Relation.Binary.PropositionalEquality

module Coso (𝕆 : Set)(O : 𝕆 → Set) -- Opaque types
    where

  -- Start defining our kinds!
  infixr 50 _⇒_
  data 𝕂 : Set where
    ⋆   : 𝕂
    _⇒_ : 𝕂 → 𝕂 → 𝕂

  -- We now map these to Set₁
  ⟦_⟧K : 𝕂 → Set₁
  ⟦ ⋆       ⟧K = Set
  ⟦ k₁ ⇒ k₂ ⟧K = ⟦ k₁ ⟧K → ⟦ k₂ ⟧K

  Constraint : 𝕂 → Set₂
  Constraint κ = ⟦ κ ⟧K → Set₁

  -- Atoms
  data Atom : 𝕂 → Set₁ where
    KA : ∀{κ} →  𝕆             → Atom κ 
    KV : ∀{κ} → (⟦ κ ⟧K → Set) → Atom κ
    -- TODO: Add the pre and post types
    KR : ∀{κ} → Atom κ
 
  -- Constructors have a list of constraints
  -- and a list of fields (called Atoms) here
  data Con : 𝕂 → Set₂ where
    con : ∀{κ}(l : List (Constraint κ)) → List (Atom κ) → Con κ

  -- A Datatype is a list of constructors
  SOP : 𝕂 → Set₂
  SOP κ = List (Con κ)

  -- * Semantics
  ⟦_⟧A : ∀{κ} → Atom κ → ⟦ κ ⟧K → Set → Set
  ⟦ KA o ⟧A X R = O o
  ⟦ KV f ⟧A X R = f X
  ⟦ KR   ⟧A X R = R

  ⟦_⟧Con : ∀{κ} → Con κ → ⟦ κ ⟧K → Set → Set₂
  ⟦ con preds as ⟧Con X R = All (λ ctr → ctr X) preds
                          × All (λ a → ⟦ a ⟧A X R) as

  ⟦_⟧S : ∀{κ} → SOP κ → ⟦ κ ⟧K → Set → Set₂
  ⟦ cs ⟧S X R = Any (λ c → ⟦ c ⟧Con X R) cs

  postulate danger : Set₂ → Set

  {-# NO_POSITIVITY_CHECK #-}
  data Fix {κ}(σ : SOP κ)(X : ⟦ κ ⟧K) : Set where
    ⟨_⟩ : danger (⟦ σ ⟧S X (Fix σ X)) → Fix σ X

-- * Example 1

  data X : Set → Set where
    XBool : Bool → X Bool

  id : ∀{a}{A : Set a} → A → A
  id x = x

  sopX : SOP ⋆
  sopX = con ((λ x → x ≡ Bool) ∷ []) 
             (KV id ∷ []) 
       ∷ []

  
  valFalse : X Bool
  valFalse = XBool false 

  valFalse' : ⟦ sopX ⟧S Bool Unit
  valFalse' = here (refl ∷ [] , {!!} ∷ [])

-- * Example 2

  data Exp : Set → Set where
    Var : ∀{A} → A → Exp A
    Add : Exp ℕ → Exp ℕ → Exp ℕ
    Cmp : Exp ℕ → Exp ℕ → Exp Bool

  sopExp : SOP ⋆
  sopExp = con [] (KR ∷ [])
         ∷ con ((λ x → x ≡ ℕ) ∷ []) (KR ∷ KR ∷ [])
         ∷ {!!}
         ∷ []
        
