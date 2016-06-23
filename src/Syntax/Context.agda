module Syntax.Context where

open import Syntax.Type

-- A context is a backwards list of types.
infixl 10 _∙_
data Context : Set where
  ε    : Context
  _∙_  : Context → Type → Context

-- A variable in that context is a de Bruijn index.
-- Here we use a type family to ensure that the index
-- is both well-scoped and well-typed.
infix 5 _∈_
infixr 5 1+_

data _∈_ (σ : Type) : Context → Set where

  zero  : {Γ : Context} →
  
          ---------------
            σ ∈ (Γ ∙ σ)
            
  1+_   : {Γ : Context} {τ : Type} →

            σ ∈ Γ →
          -------------------
            σ ∈ (Γ ∙ τ)


-- In order to have σ a PARAMETER of the inductive family,
-- Agda forces us to use the type Type → Context → Set.
-- However predicates of type Context → Type → Set are a
-- central notion of our development as hinted at by the
-- definition in Semantics.Model.
-- So we provide a flipped version of _∈_

_∋_ : Context → Type → Set
Γ ∋ σ = σ ∈ Γ
