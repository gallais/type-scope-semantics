module Semantics.CPS.CBV where

open import Syntax         as λC
open import Syntax.MoggiML as ML
open import Semantics.Model
open import Semantics.Environment as Env hiding (refl)
open import Semantics.Specification
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

mutual

  ⟦_⟧ : λC.Type → ML.Type
  ⟦ `Unit  ⟧ = `Unit
  ⟦ `Bool  ⟧ = `Bool
  ⟦ σ `→ τ ⟧ = ⟦ σ ⟧ `→ #⟦ τ ⟧

  #⟦_⟧ : λC.Type → ML.Type
  #⟦ σ ⟧ = # ⟦ σ ⟧

mutual

  ⟦⟧-inj : ∀ σ τ → ⟦ σ ⟧ ≡ ⟦ τ ⟧ → σ ≡ τ
  ⟦⟧-inj `Unit `Unit eq = refl
  ⟦⟧-inj `Bool `Bool eq = refl
  ⟦⟧-inj (σ₁ `→ τ₁) (σ₂ `→ τ₂) eq =
    let (eqσ , eqτ) = ML.`→-inj eq
    in cong₂ _`→_ (⟦⟧-inj σ₁ σ₂ eqσ) (#⟦⟧-inj τ₁ τ₂ eqτ)
  ⟦⟧-inj `Unit `Bool ()
  ⟦⟧-inj `Unit (_ `→ _) ()
  ⟦⟧-inj `Bool `Unit ()
  ⟦⟧-inj `Bool (_ `→ _) ()
  ⟦⟧-inj (_ `→ _) `Unit ()
  ⟦⟧-inj (_ `→ _) `Bool ()

  #⟦⟧-inj : ∀ σ τ → #⟦ σ ⟧ ≡ #⟦ τ ⟧ → σ ≡ τ
  #⟦⟧-inj σ τ = ⟦⟧-inj σ τ ∘ #-inj
  
Value : Model _
Value Γ σ = (⟦_⟧ λC.<$> Γ) ML.⊢ ⟦ σ ⟧

Computation : Model _
Computation Γ σ = (⟦_⟧ λC.<$> Γ) ML.⊢ #⟦ σ ⟧

CallByValue : Semantics Value Computation
CallByValue = record
  { wk     = ML.wk^⊢ ∘ Env.map ⟦_⟧ ⟦⟧-inj
  ; embed  = pack (`var ∘ λC.map ⟦_⟧)
  ; ⟦var⟧  = `return
  ; ⟦λ⟧    = λ t → `return (`λ (t extend (`var zero)))
  ; _⟦$⟧_  = λ f t → f `>>= `λ (wk^⊢ extend t `>>= `λ (`var (1+ zero) `$ `var zero))
  ; ⟦⟨⟩⟧   = `return `⟨⟩
  ; ⟦tt⟧   = `return `tt
  ; ⟦ff⟧   = `return `ff
  ; ⟦ifte⟧ = λ b l r → b `>>= `λ (`ifte (`var zero) (wk^⊢ extend l) (wk^⊢ extend r))
  }
