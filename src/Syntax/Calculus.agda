module Syntax.Calculus where

open import Syntax.Type
open import Syntax.Context Type

-- The calculus is defined in a well-scoped and well-typed
-- manner using an inductive family. A term effectively
-- correponds to a derivation in the sequent calculus.

-- Nota Bene: there are TWO proofs of Γ ⊢ `Bool corresponding
-- to true and false respectively.

infix 5 _⊢_
infixl 5 _`$_
data _⊢_ (Γ : Context) : (σ : Type) → Set where

  `var     : {σ : Type} →
  
                σ ∈ Γ →
              --------------
                Γ ⊢ σ

  _`$_     : {σ τ : Type} →

                Γ ⊢ (σ `→ τ) → Γ ⊢ σ →
              --------------------------
                Γ ⊢ τ

  `λ       : {σ τ : Type} →

                (Γ ∙ σ) ⊢ τ →
              ----------------
                Γ ⊢ (σ `→ τ)

  `⟨⟩      :
              -------------
                Γ ⊢ `Unit

  `tt `ff  :
              -------------
                Γ ⊢ `Bool

  `ifte    : {σ : Type} →
 
                Γ ⊢ `Bool → Γ ⊢ σ → Γ ⊢ σ →
              ------------------------------
                Γ ⊢ σ
