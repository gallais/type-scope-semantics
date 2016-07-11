module Syntax.Context.Core where

open import Data.Nat
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

-- A context is a backwards list
infixl 10 _∙_
data Context (A : Set) : Set where
  ε    : Context A
  _∙_  : Context A → A → Context A

-- Contexts are functorial
infixr 6 _<$>_
_<$>_ : {A B : Set} → (A → B) → Context A → Context B
f <$> ε      = ε
f <$> xs ∙ x = (f <$> xs) ∙ f x

-- A variable in that context is a de Bruijn index.
-- Here we use a type family to ensure that the index
-- is both well-scoped and well-typed.
infix 5 _∈_
infixr 5 1+_

data _∈_ {A : Set} (σ : A) : Context A → Set where

  zero  : {Γ : Context A} →
  
          ---------------
            σ ∈ (Γ ∙ σ)
            
  1+_   : {Γ : Context A} {τ : A} →

            σ ∈ Γ →
          -------------------
            σ ∈ (Γ ∙ τ)

-- In order to have σ a PARAMETER of the inductive family,
-- Agda forces us to use the type Type → Context → Set.
-- However predicates of type Context → Type → Set are a
-- central notion of our development as hinted at by the
-- definition in Semantics.Model.
-- So we provide a flipped version of _∈_
infix 5 _∋_
_∋_ : {A : Set} → Context A → A → Set
Γ ∋ σ = σ ∈ Γ

map : {A B : Set} {Γ : Context A} {σ : A} (f : A → B) → Γ ∋ σ → f <$> Γ ∋ f σ
map f zero   = zero
map f (1+ v) = 1+ map f v

map-inv : {A B : Set} {Γ : Context A} {τ : B} (f : A → B) → f <$> Γ ∋ τ → ∃ λ σ → τ ≡ f σ
map-inv f = go _ refl where

  go : ∀ Γ {Δ τ} → f <$> Γ ≡ Δ → Δ ∋ τ → ∃ λ σ → τ ≡ f σ
  go ε       ()   zero
  go ε       ()   (1+ v)
  go (Γ ∙ _) refl zero   = , refl
  go (Γ ∙ _) refl (1+ v) = go Γ refl v

map⁻¹ : {A B : Set} {Γ : Context A} {σ : A} (f : A → B) →
        (∀ σ τ → f σ ≡ f τ → σ ≡ τ) → f <$> Γ ∋ f σ → Γ ∋ σ 
map⁻¹ f inj = go _ refl refl where

  go : ∀ Γ {σ τ Δ} → f <$> Γ ≡ Δ → f σ ≡ τ → Δ ∋ τ → Γ ∋ σ
  go ε       ()   eq zero
  go ε       ()   eq (1+ v)
  go (Γ ∙ σ) refl eq zero rewrite inj _ _ eq = zero
  go (Γ ∙ σ) refl eq (1+ v) = 1+ go Γ refl eq v

-- Each context has a size
size : {A : Set} → Context A → ℕ
size ε       = zero
size (Γ ∙ _) = 1 + size Γ

