module Semantics.NormalisationByEvaluation.βιξ where

open import Syntax.Core
open import Syntax.Normal
open import Syntax.Normal.Weakening
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Function

R : Type → Set
R _ = ⊤

infix 5 _⊨_ _⊨⋆_
mutual

  _⊨_   : Model _
  Γ ⊨ σ  = Γ ⊢[ R ]^ne σ ⊎ Γ ⊨⋆ σ

  _⊨⋆_  : Model _
  Γ ⊨⋆ `Unit     = ⊤
  Γ ⊨⋆ `Bool     = Bool
  Γ ⊨⋆ (σ `→ τ)  = {Δ : Context} → Renaming Γ Δ → Δ ⊨ σ → Δ ⊨ τ

wk^⊨⋆ : Weakening _⊨⋆_
wk^⊨⋆ {σ = `Unit}  ren T = T
wk^⊨⋆ {σ = `Bool}  ren T = T
wk^⊨⋆ {σ = σ `→ τ} ren T = λ inc → T (trans ren inc)

wk^⊨ : Weakening _⊨_
wk^⊨ ren (inj₁ ne)  = inj₁ $ wk^ne ren ne
wk^⊨ ren (inj₂ T)   = inj₂ $ wk^⊨⋆ ren T

reflect : Reflect R _⊨_
reflect σ = inj₁

mutual

  reify⋆ : Reify R _⊨⋆_
  reify⋆ `Unit     T = `⟨⟩
  reify⋆ `Bool     T = if T then `tt else `ff
  reify⋆ (σ `→ τ)  T = `λ (reify τ (T (step refl) var‿0))
    where var‿0 = inj₁ $ `var zero

  reify : Reify R _⊨_
  reify σ (inj₁ ne)  = `neu _ ne
  reify σ (inj₂ T)   = reify⋆ σ T

infixr 5 _$$_
_$$_ : Applicative _⊨_
(inj₁ ne) $$ u = inj₁ $ ne `$ reify _ u
(inj₂ F)  $$ u = F refl u

ifte : {Γ : Context} {σ : Type} → Γ ⊨ `Bool → Γ ⊨ σ → Γ ⊨ σ → Γ ⊨ σ
ifte (inj₁ ne) l r = inj₁ $ `ifte ne (reify _ l) (reify _ r)
ifte (inj₂ T)  l r = if T then l else r

Normalise : Semantics _⊨_ _⊨_
Normalise = record
  { embed = pack (reflect _ ∘ `var); wk = wk^⊨; ⟦var⟧   = id
  ; _⟦$⟧_ = _$$_; ⟦λ⟧ = inj₂
  ; ⟦⟨⟩⟧ = inj₂ tt; ⟦tt⟧ = inj₂ true; ⟦ff⟧ = inj₂ false; ⟦ifte⟧  = ifte }
          
norm : Normalisation R
norm t = reify _ $ Fundamental.lemma' Normalise t
