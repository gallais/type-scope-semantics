module Properties.Relation.βιξη where

open import Syntax.Core
open import Syntax.Normal
open import Syntax.Normal.Weakening
open import Semantics.Environment as Env
open import Semantics.NormalisationByEvaluation.βιξη
open import Properties.Relation

open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as PEq

EQREL : (Γ : Context) (σ : Type) (T U : Γ ⊨ σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U =
  {Δ : Context} (inc : Renaming Γ Δ) {V W : Δ ⊨ σ} →
  EQREL Δ σ V W → EQREL Δ τ (T inc V) (U inc W)

_≣_ : RModel _ _⊨_ _⊨_
_≣_ = mkRModel (λ {Γ} {σ} → EQREL Γ σ)

sym≣ : Symmetric _≣_
sym≣ {σ = `Unit}  eq = tt
sym≣ {σ = `Bool}  eq = sym eq
sym≣ {σ = σ `→ τ} eq = λ inc eqVW → sym≣ (eq inc (sym≣ eqVW))

mutual

  trans≣ : Transitive _≣_
  trans≣ {σ = `Unit}  eq₁ eq₂ = tt
  trans≣ {σ = `Bool}  eq₁ eq₂ = PEq.trans eq₁ eq₂
  trans≣ {σ = σ `→ τ} eq₁ eq₂ = λ inc eqVW → trans≣ (eq₁ inc (refl≣ eqVW)) (eq₂ inc eqVW)

  refl≣ : {Γ : Context} {σ : Type} {S T : Γ ⊨ σ} → related _≣_ S T → related _≣_ S S
  refl≣ eq = trans≣ eq (sym≣ eq)

wk^≣ :  {Δ Γ : Context} {σ : Type} (ren : Renaming Γ Δ) {T U : Γ ⊨ σ} →
  related _≣_ T U → related _≣_ (wk^⊨ ren T) (wk^⊨ ren U)
wk^≣ {σ = `Unit}  ren eq = tt
wk^≣ {σ = `Bool}  ren eq = cong (wk^nf ren) eq
wk^≣ {σ = σ `→ τ} ren eq = λ inc eqVW → eq (Env.trans ren inc) eqVW

wk^⊨-trans :
  ∀ {σ Γ Δ Θ} inc₁ (inc₂ : Renaming Δ Θ) {T U : Γ ⊨ σ} →
  EQREL Γ σ T U → EQREL Θ σ (wk^⊨ inc₂ $ wk^⊨ inc₁ T) (wk^⊨ (Env.trans inc₁ inc₂) U)
wk^⊨-trans {σ = `Unit}  inc₁ inc₂ eq = tt
wk^⊨-trans {σ = `Bool}  inc₁ inc₂ eq rewrite eq = wk^nf-trans _
wk^⊨-trans {σ = σ `→ τ} inc₁ inc₂ eq = λ inc → eq _

mutual

  reify^≣ : {Γ : Context} (σ : Type) {T U : Γ ⊨ σ} →
            related _≣_ T U → reify σ T ≡ reify σ U
  reify^≣ `Unit    R = PEq.refl
  reify^≣ `Bool    R = R
  reify^≣ (σ `→ τ) R = cong `λ (reify^≣ τ (R (step Env.refl) (reflect^≣ σ PEq.refl)))

  reflect^≣ : {Γ : Context} (σ : Type) {t u : Γ ⊢[ R ]^ne σ} →
              t ≡ u → related _≣_ (reflect σ t) (reflect σ u)
  reflect^≣ `Unit    eq = tt
  reflect^≣ `Bool    eq = cong (`neu tt) eq
  reflect^≣ (σ `→ τ) eq = λ ren eq′ →
    reflect^≣ τ $ cong₂ (_`$_ ∘ wk^ne ren) eq $ reify^≣ σ eq′
