module Syntax.Core.Examples where

open import Syntax.Core

VAR0 : {Γ : Context} {σ : Type} → (Γ ∙ σ) ⊢ σ
VAR0 = `var zero

APP : {Γ : Context} {σ τ : Type} → (Γ ∙ (σ `→ τ) ∙ σ) ⊢ τ
APP = `var (1+ zero) `$ `var zero

ID : {Γ : Context} {σ : Type} → Γ ⊢ (σ `→ σ)
ID = `λ VAR0

TRUE : {Γ : Context} {σ τ : Type} → Γ ⊢ (σ `→ τ `→ σ)
TRUE = `λ (`λ (`var (1+ zero)))

FALSE : {Γ : Context} {σ τ : Type} → Γ ⊢ (σ `→ τ `→ τ)
FALSE = `λ ID

IFTE : {Γ : Context} {σ : Type} → Γ ⊢ (`Bool `→ (σ `→ σ `→ σ))
IFTE = `λ (`ifte (`var zero) TRUE FALSE)

THUNK : {Γ : Context} {σ : Type} → Γ ⊢ (σ `→ (`Unit `→ σ))
THUNK = TRUE

FORCE : {Γ : Context} {σ : Type} → Γ ⊢ ((`Unit `→ σ) `→ σ)
FORCE = `λ (`var zero `$ `⟨⟩)

ID' : {Γ : Context} {σ : Type} → Γ ⊢ (σ `→ σ)
ID' = FORCE `$ (THUNK `$ ID)
