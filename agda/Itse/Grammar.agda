module Itse.Grammar where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary
open import Data.List
open import Data.Maybe
open import Data.String
open import Data.Empty

data ExprVari : Set
Prgm : Set
data Stmt : Set
data Expr : ExprVari → Set
data Name : ExprVari → Set

data ExprVari where
  s : ExprVari -- sort
  k : ExprVari -- kind
  p : ExprVari -- type
  t : ExprVari -- term

_≟-ExprVari_ : ∀ (e : ExprVari) (e′ : ExprVari) → Dec (e ≡ e′)

TypeOf : ExprVari → ExprVari
TypeOf s = s
TypeOf k = s
TypeOf p = k
TypeOf t = p

Kind : Set
Type : Set
Term : Set
Nameₚ : Set
Nameₜ : Set

Sort = Expr s
Kind = Expr k
Type = Expr p
Term = Expr t
Nameₚ = Name p 
Nameₜ = Name t

Prgm = List Stmt

infixr 10 `defnₚ_⦂_≔_ `defnₚ_⦂_≔_
infixr 11 _`→_
infixr 12 `λₖₚ[_⦂_]_ `λₖₜ[_⦂_]_ `λₚₚ[_⦂_]_ `λₚₜ[_⦂_]_ `λₜₚ[_⦂_]_ `λₜₜ[_⦂_]_
infixr 13 _`∙ₚₚ_ _`∙ₚₜ_ _`∙ₜₚ_ _`∙ₜₜ_
infixr 14 `ₚ_ `ₜ_

data Stmt where
  `defnₚ_⦂_≔_ : Nameₚ → Kind → Type → Stmt
  `defnₜ_⦂_≔_ : Nameₜ → Type → Term → Stmt

data Expr where
  -- sort
  `□ₛ : Sort
  -- kind
  `●ₖ : Kind
  `λₖₚ[_⦂_]_ : Nameₚ → Kind → Kind → Kind
  `λₖₜ[_⦂_]_ : Nameₜ → Type → Kind → Kind
  -- p
  `ₚ_        : Nameₚ → Type
  `λₚₚ[_⦂_]_ : Nameₚ → Kind → Type → Type
  `λₚₜ[_⦂_]_ : Nameₜ → Type → Type → Type
  _`∙ₚₚ_     : Type → Type → Type
  _`∙ₚₜ_     : Type → Term → Type
  `ι[_]_     : Nameₜ → Type → Type
  -- t
  `ₜ_        : Nameₜ → Term
  `λₜₚ[_⦂_]_ : Nameₚ → Kind → Term → Term
  `λₜₜ[_⦂_]_ : Nameₜ → Type → Term → Term
  _`∙ₜₚ_     : Term → Type → Term
  _`∙ₜₜ_     : Term → Term → Term
  
data Name where
  nameₚ : Maybe String → Nameₚ
  nameₜ : Maybe String → Nameₜ

postulate
  _≟-Name_ : ∀ {e} (n : Name e) → (n′ : Name e) → Dec (n ≡ n′)

s ≟-ExprVari s = yes refl
s ≟-ExprVari k = no λ ()
s ≟-ExprVari p = no λ ()
s ≟-ExprVari t = no λ ()
k ≟-ExprVari s = no λ ()
k ≟-ExprVari k = yes refl
k ≟-ExprVari p = no λ ()
k ≟-ExprVari t = no λ ()
p ≟-ExprVari s = no λ ()
p ≟-ExprVari k = no λ ()
p ≟-ExprVari p = yes refl
p ≟-ExprVari t = no λ ()
t ≟-ExprVari s = no λ ()
t ≟-ExprVari k = no λ ()
t ≟-ExprVari p = no λ ()
t ≟-ExprVari t = yes refl

_`→_ : Type → Type → Type
α `→ β = `λₚₜ[ nameₜ nothing ⦂ α ] β
