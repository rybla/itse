module Itse.Checking where

open import Itse.Grammar
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Bool
open import Data.List hiding (lookup)
open import Data.Product
open import Data.Maybe

{-
# Checking

-}

{-
## Context

-}

data Context : Set
Closure : Set

infixr 6 _⦂_,_ [_],_

data Context where
  ∅ : Context
  _⦂_,_ : ∀ {e} → Name e → Expr (TypeOf e) → Context → Context
  [_],_ : Closure → Context → Context

{-
## Closure

-}

Closure = List (∃[ e ] (Name e × Expr e × Expr (TypeOf e)))

lookup-μ : ∀ {e} → Name e → Closure → Maybe (Expr e × Expr (TypeOf e))
lookup-μ {p} ξ []                    = nothing
lookup-μ {p} ξ ((p , υ , α , A) ∷ μ) with ξ ≟-Name υ
lookup-μ {p} ξ ((p , υ , α , A) ∷ μ)    | yes refl = just (α , A)
lookup-μ {p} ξ ((p , υ , α , A) ∷ μ)    | no  _    = lookup-μ ξ μ
lookup-μ {p} ξ ((t , _)         ∷ μ) = lookup-μ ξ μ
lookup-μ {t} x []                    = nothing
lookup-μ {t} x ((p , _)         ∷ μ) = lookup-μ x μ
lookup-μ {t} x ((t , y , a , α) ∷ μ) with x ≟-Name y
lookup-μ {t} x ((t , y , a , α) ∷ μ)    | yes refl = just (a , α)
lookup-μ {t} x ((t , y , a , α) ∷ μ)    | no  _    = lookup-μ x μ

lookup : ∀ {e} → Name e → Context → Maybe (Expr e × Expr (TypeOf e))
lookup x ∅ = nothing
lookup x (_ ⦂ _ , Γ) = lookup x Γ
lookup x ([ μ  ], Γ) = lookup-μ x μ

{-
## Substitution

-}

infix 6 ⟦_↦_⟧_


⟦_↦_⟧_ : ∀ {e e′} → Name e → Expr e → Expr e′ → Expr e′
⟦_↦_⟧_ = {!!}


{-
## Wellformed-ness

-}

infix 5 _⊢wf _⊢_ok _⊢_⦂_

data _⊢wf : Context → Set
data _⊢_ok : Context → Closure → Set
data _⊢_⦂_ : ∀ {e} → Context → Expr e → Expr (TypeOf e) → Set

data _⊢wf where

  ∅⊢wf :
    ∅ ⊢wf

  judgeₚ : ∀ {Γ} {X : Kind} {ξ} →
    Γ ⊢wf →
    Γ ⊢ X ⦂ `□ₛ →
    ----
    ξ ⦂ X , Γ ⊢wf

  judgeₜ : ∀ {Γ} {ξ : Type} {x : Nameₜ} → 
    Γ ⊢wf →
    Γ ⊢ ξ ⦂ `●ₖ → 
    ----
    x ⦂ ξ , Γ ⊢wf

  closure : ∀ {Γ} {μ} →
    Γ ⊢wf →
    Γ ⊢ μ ok →
    [ μ ], Γ ⊢wf

-- Closure = List (∃[ e ] ∃[ e≢k ] (Name e × Expr e × Expr (TypeOf e {e≢k})))
data _⊢_ok where

  -- type :
  --   Γ ⊢ μ ok →
  --   [ μ ], Γ ⊢

data _⊢_⦂_ where

  -- sorting (well-formed kinds)

  ●ₖ : ∀ {Γ} →
    Γ ⊢ `●ₖ ⦂ `□ₛ

  λₖₚ-intro : ∀ {Γ} {ξ} {X A} →
    ξ ⦂ X , Γ ⊢ A ⦂ `□ₛ →
    Γ ⊢ X ⦂ `□ₛ →
    ----
    Γ ⊢ `λₖₚ[ ξ ⦂ X ] A ⦂ `□ₛ

  λₖₜ-intro : ∀ {Γ} {ξ} {A} {x} →
    x ⦂ ξ , Γ ⊢ A ⦂ `□ₛ →
    Γ ⊢ ξ ⦂ `●ₖ →
    ----
    Γ ⊢ `λₖₜ[ x ⦂ ξ ] A ⦂ `□ₛ

  -- kinding

  λₚₚ-intro : ∀ {Γ} {X} {β} {ξ} →
    Γ ⊢ X ⦂ `□ₛ →
    ξ ⦂ X , Γ ⊢ β ⦂ `●ₖ →
    ----
    Γ ⊢ `λₚₚ[ ξ ⦂ X ] β ⦂ `λₖₚ[ ξ ⦂ X ] `●ₖ

  λₚₜ-intro : ∀ {Γ} {ξ} {β} {x} →
    Γ ⊢ ξ ⦂ `●ₖ →
    x ⦂ ξ , Γ ⊢ β ⦂ `●ₖ →
    ----
    Γ ⊢ `λₚₜ[ x ⦂ ξ ] β ⦂ `λₖₜ[ x ⦂ ξ ] `●ₖ

  λₚₚ-elim : ∀ {Γ} {A B} {ξ φ α} →
    Γ ⊢ φ ⦂ `λₖₚ[ ξ ⦂ A ] B →
    Γ ⊢ α ⦂ A →
    ----
    Γ ⊢ φ `∙ₚₚ α ⦂ B

  λₚₜ-elim : ∀ {Γ} {B} {φ α} {a} {x} →
    Γ ⊢ φ ⦂ `λₖₜ[ x ⦂ α ] B →
    Γ ⊢ a ⦂ α →
    ----
    Γ ⊢ φ `∙ₚₜ a ⦂ B

  -- typing

  λₜₚ-intro : ∀ {Γ} {X} {α} {a} {ξ} →
    Γ ⊢ X ⦂ `□ₛ →
    ξ ⦂ X , Γ ⊢ a ⦂ α →
    ----
    Γ ⊢ `λₜₚ[ ξ ⦂ X ] a ⦂ `λₚₚ[ ξ ⦂ X ] α

  λₜₜ-intro : ∀ {Γ} {α ξ} {a} {x} →
    Γ ⊢ α ⦂ `●ₖ → 
    x ⦂ ξ , Γ ⊢ a ⦂ α →
    ----
    Γ ⊢ `λₜₜ[ x ⦂ ξ ] a ⦂ `λₚₜ[ x ⦂ ξ ] α

  λₜₚ-elim : ∀ {Γ} {A} {α β} {f} {ξ} →
    Γ ⊢ f ⦂ `λₚₚ[ ξ ⦂ A ] β →
    Γ ⊢ α ⦂ A →
    ----
    Γ ⊢ f `∙ₜₚ α ⦂ β

  λₜₜ-elim : ∀ {Γ} {α β} {f a x} →
    Γ ⊢ f ⦂ `λₚₜ[ x ⦂ α ] β →
    Γ ⊢ a ⦂ α →
    ----
    Γ ⊢ f `∙ₜₜ a ⦂ β

  -- "SelfGen"
  ι-intro : ∀ {Γ} {α} {a} {x} →
    Γ ⊢ a ⦂ ⟦ x ↦ a ⟧ α → 
    Γ ⊢ `ι[ x ] α ⦂ `●ₖ →
    ----
    Γ ⊢ a ⦂ `ι[ x ] α

  -- "SelfInst"
  ι-elim : ∀ {Γ} {α} {a} {x} →
    Γ ⊢ a ⦂ `ι[ x ] α →
    ----
    Γ ⊢ a ⦂ ⟦ x ↦ a ⟧ α
    

