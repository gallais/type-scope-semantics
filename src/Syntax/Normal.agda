module Syntax.Normal where

open import Syntax.Core

infix 5 _⊢[_]^ne_ _⊢[_]^nf_
mutual

  data _⊢[_]^ne_ (Γ : Context) (R : Type → Set) (σ : Type) : Set where
    `var   : (v : σ ∈ Γ) → Γ ⊢[ R ]^ne σ
    _`$_   : {τ : Type} (t : Γ ⊢[ R ]^ne τ `→ σ) (u : Γ ⊢[ R ]^nf τ) → Γ ⊢[ R ]^ne σ
    `ifte  : (b : Γ ⊢[ R ]^ne `Bool) (l r : Γ ⊢[ R ]^nf σ) → Γ ⊢[ R ]^ne σ

  data _⊢[_]^nf_ (Γ : Context) (R : Type → Set) : (σ : Type) → Set where
    `neu    : {σ : Type} (pr : R σ) (t : Γ ⊢[ R ]^ne σ) → Γ ⊢[ R ]^nf σ
    `⟨⟩     : Γ ⊢[ R ]^nf `Unit
    `tt     : Γ ⊢[ R ]^nf `Bool
    `ff     : Γ ⊢[ R ]^nf `Bool
    `λ      : {σ τ : Type} (b : Γ ∙ σ ⊢[ R ]^nf τ) → Γ ⊢[ R ]^nf (σ `→ τ)

Normalisation : (Type → Set) → Set
Normalisation R = {Γ : Context} {σ : Type} → Γ ⊢ σ → Γ ⊢[ R ]^nf σ

infix 5 _⊢^whne_ _⊢^whnf_
data _⊢^whne_ (Γ : Context) (σ : Type) : Set where
  `var   : (v : σ ∈ Γ) → Γ ⊢^whne σ
  _`$_   : {τ : Type} (t : Γ ⊢^whne (τ `→ σ)) (u : Γ ⊢ τ) → Γ ⊢^whne σ
  `ifte  : (b : Γ ⊢^whne `Bool) (l r : Γ ⊢ σ) → Γ ⊢^whne σ

data _⊢^whnf_ (Γ : Context) : (σ : Type) → Set where
  `whne    : {σ : Type} (t : Γ ⊢^whne σ) → Γ ⊢^whnf σ
  `⟨⟩      : Γ ⊢^whnf `Unit
  `tt `ff  : Γ ⊢^whnf `Bool
  `λ       : {σ τ : Type} (b : Γ ∙ σ ⊢ τ) → Γ ⊢^whnf (σ `→ τ)

erase^whne : {Γ : Context} {σ : Type} (t : Γ ⊢^whne σ) → Γ ⊢ σ
erase^whne (`var v)       = `var v
erase^whne (t `$ u)       = erase^whne t `$ u
erase^whne (`ifte t l r)  = `ifte (erase^whne t) l r
