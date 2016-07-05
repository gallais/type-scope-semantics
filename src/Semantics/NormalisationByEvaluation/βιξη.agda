module Semantics.NormalisationByEvaluation.βιξη where

open import Syntax.Core
open import Syntax.Normal
open import Syntax.Normal.Weakening
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification

open import Data.Empty
open import Data.Unit
open import Function

R : Type → Set
R `Bool  = ⊤
R _      = ⊥

infix 5 _⊨_

_⊨_ : Model _
Γ ⊨ `Unit     = ⊤
Γ ⊨ `Bool     = Γ ⊢[ R ]^nf `Bool
Γ ⊨ (σ `→ τ)  = {Δ : Context} → Renaming Γ Δ → Δ ⊨ σ → Δ ⊨ τ

wk^⊨ : Weakening _⊨_
wk^⊨ {σ = `Unit}  ren T = T
wk^⊨ {σ = `Bool}  ren T = wk^nf ren T
wk^⊨ {σ = σ `→ τ} ren T = λ inc → T (trans ren inc)

infixr 5 _$$_
_$$_ : Applicative _⊨_
t $$ u = t refl u

mutual

  var‿0 : {Γ : Context} {σ : Type} → Γ ∙ σ ⊨ σ
  var‿0 = reflect _ (`var zero)

  reflect : Reflect R _⊨_
  reflect `Unit     t = tt
  reflect `Bool     t = `neu _ t
  reflect (σ `→ τ)  t = λ inc u → reflect τ (wk^ne inc t `$ reify σ u)

  reify : Reify R _⊨_
  reify `Unit     T = `⟨⟩
  reify `Bool     T = T
  reify (σ `→ τ)  T = `λ (reify τ (T extend var‿0))

ifte : {Γ : Context} {σ : Type} → Γ ⊨ `Bool → Γ ⊨ σ → Γ ⊨ σ → Γ ⊨ σ
ifte `tt         l r = l
ifte `ff         l r = r
ifte (`neu _ T)  l r = reflect _ (`ifte T (reify _ l) (reify _ r))

Normalise : Semantics _⊨_ _⊨_
Semantics.wk     Normalise = wk^⊨
Semantics.embed  Normalise = pack (reflect _ ∘ `var)
Semantics.⟦var⟧  Normalise = id
Semantics.⟦λ⟧    Normalise = id
Semantics._⟦$⟧_  Normalise = _$$_
Semantics.⟦⟨⟩⟧   Normalise = tt
Semantics.⟦tt⟧   Normalise = `tt
Semantics.⟦ff⟧   Normalise = `ff
Semantics.⟦ifte⟧ Normalise = ifte

eval : Evaluation _ _
eval = Fundamental.lemma Normalise

eval' : Evaluation' _
eval' = Fundamental.lemma' Normalise

norm : ∀ {Γ Δ σ} → Γ ⊢ σ → Var Γ ⇒[ _⊨_ ] Δ → Δ ⊢[ R ]^nf σ
norm t ρ = reify _ $ eval t ρ

norm' : Normalisation R
norm' t = reify _ $ eval' t
