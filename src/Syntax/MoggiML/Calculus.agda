module Syntax.MoggiML.Calculus where

open import Syntax.MoggiML.Type
open import Syntax.Context Type
open import Semantics.Environment.Core

infix 5 _⊢_
data _⊢_ (Γ : Context) : Type → Set where

  `var     : {σ : Type} →
  
                σ ∈ Γ →
              --------------
                Γ ⊢ σ

  _`$_     : {σ τ : Type} →

                Γ ⊢ (σ `→ # τ) → Γ ⊢ σ →
              --------------------------
                Γ ⊢ # τ

  `λ       : {σ τ : Type} →

                (Γ ∙ σ) ⊢ # τ →
              ----------------
                Γ ⊢ (σ `→ # τ)

  `⟨⟩      :
              -------------
                Γ ⊢ `Unit

  `tt `ff  :
              -------------
                Γ ⊢ `Bool

  `ifte    : {σ : Type} →
 
                Γ ⊢ `Bool → Γ ⊢ # σ → Γ ⊢ # σ →
              ------------------------------
                Γ ⊢ # σ

  _`>>=_ : {σ τ : Type} →

                Γ ⊢ # σ → Γ ⊢ (σ `→ # τ) →
              ------------------------------
                Γ ⊢ # τ

  `return : {σ : Type} →

                Γ ⊢ σ →
              -------------
                Γ ⊢ # σ

wk^⊢ : Weakening Type _⊢_
wk^⊢ inc (`var v)      = `var (lookup inc v)
wk^⊢ inc (f `$ t)      = wk^⊢ inc f `$ wk^⊢ inc t
wk^⊢ inc (`λ t)        = `λ (wk^⊢ (pop! inc) t)
wk^⊢ inc `⟨⟩           = `⟨⟩
wk^⊢ inc `tt           = `tt
wk^⊢ inc `ff           = `ff
wk^⊢ inc (`ifte b l r) = `ifte (wk^⊢ inc b) (wk^⊢ inc l) (wk^⊢ inc r)
wk^⊢ inc (m `>>= f)    = wk^⊢ inc m `>>= wk^⊢ inc f
wk^⊢ inc (`return a)   = `return (wk^⊢ inc a)
