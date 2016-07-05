module Semantics.NormalisationByEvaluation.βι where

open import Syntax.Core
open import Syntax.Normal
open import Syntax.Normal.Weakening
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification
open import Semantics.Syntactic.Instances

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Function

infix 5 _⊨_ _⊨⋆_

mutual

  _⊨_ : Model _
  Γ ⊨ σ  = Γ ⊢ σ × (Γ ⊢^whne σ ⊎ Γ ⊨⋆ σ)

  _⊨⋆_ : Model _
  Γ ⊨⋆ `Unit     = ⊤
  Γ ⊨⋆ `Bool     = Bool
  Γ ⊨⋆ (σ `→ τ)  = {Δ : Context} → Renaming Γ Δ → Δ ⊨ σ → Δ ⊨ τ

wk⋆ : Weakening _⊨⋆_
wk⋆ {σ = `Unit } ren T = T
wk⋆ {σ = `Bool } ren T = T
wk⋆ {σ = σ `→ τ} ren T = λ inc → T (trans ren inc)

wk : Weakening _⊨_
wk inc (t , inj₁ ne)  = rename inc t , inj₁ (wk^whne inc ne)
wk inc (t , inj₂ T)   = rename inc t , inj₂ (wk⋆ inc T)

reflect : {Γ : Context} (σ : Type) → Γ ⊢^whne σ → Γ ⊨ σ
reflect σ t = erase^whne t , inj₁ t

mutual

  reify⋆ : {Γ : Context} (σ : Type) → Γ ⊨⋆ σ → Γ ⊢^whnf σ
  reify⋆ `Unit     T = `⟨⟩
  reify⋆ `Bool     T = if T then `tt else `ff
  reify⋆ (σ `→ τ)  T = `λ $ proj₁ $ T extend var‿0
    where var‿0 = reflect _ $ `var zero

  reify : {Γ : Context} (σ : Type) → Γ ⊨ σ → Γ ⊢^whnf σ
  reify σ (t , inj₁ ne) = `whne ne
  reify σ (_ , inj₂ T)  = reify⋆ σ T

infixr 5 _$$_
_$$_ : Applicative _⊨_
(t , inj₁ ne)  $$ (u , U) = t `$ u , inj₁ (ne `$ u)
(t , inj₂ T)   $$ (u , U) = t `$ u , proj₂ (T refl (u , U))

ifte : {Γ : Context} {σ : Type} → Γ ⊨ `Bool → Γ ⊨ σ → Γ ⊨ σ → Γ ⊨ σ
ifte (b , inj₁ ne)  (l , L) (r , R) = `ifte b l r , inj₁ (`ifte ne l r)
ifte (b , inj₂ B)   (l , L) (r , R) = `ifte b l r , (if B then L else R)

Normalise : Semantics _⊨_ _⊨_
Normalise = record
  { embed = pack (reflect _ ∘ `var); wk = wk; ⟦var⟧ = id
  ; _⟦$⟧_ = _$$_; ⟦λ⟧ = λ t → `λ (proj₁ $ t extend (reflect _ $ `var zero)) , inj₂ t
  ; ⟦⟨⟩⟧ = `⟨⟩ , inj₂ tt; ⟦tt⟧ = `tt  , inj₂ true; ⟦ff⟧ = `ff  , inj₂ false; ⟦ifte⟧  = ifte }

eval : Evaluation _ _
eval = Fundamental.lemma Normalise

eval' : Evaluation' _
eval' = Fundamental.lemma' Normalise

norm : {Γ : Context} {σ : Type} → Γ ⊢ σ → Γ ⊢^whnf σ
norm t = reify _ $ eval' t
