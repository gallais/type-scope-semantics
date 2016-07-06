module Semantics.Embedding where

open import Syntax.Core
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Function

type : Type → Set
type `Unit    = ⊤
type `Bool    = Bool
type (σ `→ τ) = type σ → type τ

context : Context → Set
context ε       = ⊤
context (Γ ∙ σ) = context Γ × type σ

assumption : ∀ {Γ σ} → σ ∈ Γ → context Γ → type σ
assumption zero   (_ , s) = s
assumption (1+ v) (ρ , _) = assumption v ρ

contra : ∀ {Γ Δ} → Renaming Γ Δ → context Δ → context Γ
contra {ε}     ren ρ = tt
contra {Γ ∙ σ} ren ρ = contra (pack (lookup ren ∘ 1+_)) ρ
                     , assumption (lookup ren zero) ρ

Agda : Model _
Agda Γ σ = context Γ → type σ

wk^Agda : Weakening Agda
wk^Agda ren t = t ∘ contra ren

Embedding : Semantics Agda Agda
Semantics.wk     Embedding = wk^Agda
Semantics.embed  Embedding = pack assumption
Semantics.⟦var⟧  Embedding = id
Semantics.⟦λ⟧    Embedding = λ r ρ v → r refl (const v) ρ
Semantics._⟦$⟧_  Embedding = λ f t ρ → f ρ (t ρ) -- this is the S combinator!
Semantics.⟦⟨⟩⟧   Embedding = const tt
Semantics.⟦tt⟧   Embedding = const true
Semantics.⟦ff⟧   Embedding = const false
Semantics.⟦ifte⟧ Embedding = λ b l r ρ → (if b ρ then l else r) ρ

eval' : Evaluation' Agda
eval' = Fundamental.lemma' Embedding
