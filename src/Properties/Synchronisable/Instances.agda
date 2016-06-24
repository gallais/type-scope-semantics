module Properties.Synchronisable.Instances where

open import Syntax
open import Syntax.Normal.Weakening
open import Semantics.Environment as Env hiding (refl ; trans)
open import Semantics.Specification using (module Semantics)
open import Semantics.Instances
open import Properties.Relation
open import Properties.Synchronisable

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

SynchronisableRenamingSubstitution :
  Synchronisable 𝓢^Renaming 𝓢^Substitution (mkRModel (λ v t → `var v ≡ t)) (mkRModel _≡_)
SynchronisableRenamingSubstitution =
  record
    { 𝓔^R‿wk  = λ ren ρ^R → pack^R $ cong (rename ren) ∘ lookup^R ρ^R
    ; R⟦var⟧    = λ v ρ^R → lookup^R ρ^R v
    ; R⟦$⟧      = cong₂ _`$_
    ; R⟦λ⟧      = λ r → cong `λ (r _ refl)
    ; R⟦⟨⟩⟧     = refl
    ; R⟦tt⟧     = refl
    ; R⟦ff⟧     = refl
    ; R⟦ifte⟧   = λ eqb eql → cong₂ (uncurry `ifte) (cong₂ _,_ eqb eql)
    }

RenamingIsASubstitution :
  {Γ Δ : Context} {σ : Type} (t : Γ ⊢ σ) (ρ : Renaming Γ Δ) →
  rename ρ t ≡ substitute t (`var <$> ρ)
RenamingIsASubstitution t ρ = corollary t (pack^R $ λ _ → refl)
  where corollary = Fundamental.lemma SynchronisableRenamingSubstitution 

open import Data.Unit

EQREL : (Γ : Context) (σ : Type) (T U : Γ βιξη.⊨ σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U =
  {Δ : Context} (inc : Renaming Γ Δ) {V W : Δ βιξη.⊨ σ} →
  EQREL Δ σ V W → EQREL Δ τ (T inc V) (U inc W)

_≣_ : RModel _ βιξη._⊨_ βιξη._⊨_
_≣_ = mkRModel (λ {Γ} {σ} → EQREL Γ σ)

sym≣ : Symmetric _≣_
sym≣ {σ = `Unit}  eq = tt
sym≣ {σ = `Bool}  eq = sym eq
sym≣ {σ = σ `→ τ} eq = λ inc eqVW → sym≣ (eq inc (sym≣ eqVW))

mutual

  trans≣ : Transitive _≣_
  trans≣ {σ = `Unit}  eq₁ eq₂ = tt
  trans≣ {σ = `Bool}  eq₁ eq₂ = trans eq₁ eq₂
  trans≣ {σ = σ `→ τ} eq₁ eq₂ = λ inc eqVW → trans≣ (eq₁ inc (refl≣ eqVW)) (eq₂ inc eqVW)

  refl≣ : {Γ : Context} {σ : Type} {S T : Γ βιξη.⊨ σ} → related _≣_ S T → related _≣_ S S
  refl≣ eq = trans≣ eq (sym≣ eq)

wk^≣ :  {Δ Γ : Context} {σ : Type} (ren : Renaming Γ Δ) {T U : Γ βιξη.⊨ σ} →
  related _≣_ T U → related _≣_ (βιξη.wk^⊨ ren T) (βιξη.wk^⊨ ren U)
wk^≣ {σ = `Unit}  ren eq = tt
wk^≣ {σ = `Bool}  ren eq = cong (wk^nf ren) eq
wk^≣ {σ = σ `→ τ} ren eq = λ inc eqVW → eq (Env.trans ren inc) eqVW

mutual

  reify^≣ : {Γ : Context} (σ : Type) {T U : Γ βιξη.⊨ σ} →
            related _≣_ T U → βιξη.reify σ T ≡ βιξη.reify σ U
  reify^≣ `Unit    R = refl
  reify^≣ `Bool    R = R
  reify^≣ (σ `→ τ) R = cong `λ (reify^≣ τ (R (step Env.refl) (reflect^≣ σ refl)))

  reflect^≣ : {Γ : Context} (σ : Type) {t u : Γ ⊢[ βιξη.R ]^ne σ} →
              t ≡ u → related _≣_ (βιξη.reflect σ t) (βιξη.reflect σ u)
  reflect^≣ `Unit    eq = tt
  reflect^≣ `Bool    eq = cong (`neu tt) eq
  reflect^≣ (σ `→ τ) eq = λ ren eq′ →
    reflect^≣ τ $ cong₂ (_`$_ ∘ wk^ne ren) eq $ reify^≣ σ eq′

ifteRelNorm :
  let open Semantics βιξη.Normalise in
  {Γ : Context} {σ : Type} {b^A b^B : Γ βιξη.⊨ `Bool} {l^A l^B r^A r^B : Γ βιξη.⊨ σ} →
  related _≣_ b^A b^B → related _≣_ l^A l^B → related _≣_ r^A r^B →
  related _≣_ (⟦ifte⟧ b^A l^A r^A) (⟦ifte⟧ b^B l^B r^B)
ifteRelNorm {b^A = `tt}       refl l^R r^R = l^R
ifteRelNorm {b^A = `ff}       refl l^R r^R = r^R
ifteRelNorm {b^A = `neu _ ne} refl l^R r^R =
  reflect^≣ _ (cong₂ (`ifte ne) (reify^≣ _ l^R) (reify^≣ _ r^R))

SynchronisableNormalise :  Synchronisable βιξη.Normalise βιξη.Normalise _≣_ _≣_
SynchronisableNormalise =
  record  { 𝓔^R‿wk  = λ ren ρ^R → pack^R $ wk^≣ ren ∘ lookup^R ρ^R
          ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
          ; R⟦$⟧     = λ f → f Env.refl
          ; R⟦λ⟧     = λ r → r
          ; R⟦⟨⟩⟧    = tt
          ; R⟦tt⟧    = refl
          ; R⟦ff⟧    = refl
          ; R⟦ifte⟧  = ifteRelNorm
          }
