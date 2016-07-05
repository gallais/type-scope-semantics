module Semantics.Syntactic.Specification where

open import Syntax.Core
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification as Semantics hiding (module Fundamental)

record Syntactic {ℓ : Level} (𝓔 : Model ℓ) : Set ℓ where
  field  embed  : {Γ : Context} → Var Γ ⇒[ 𝓔 ] Γ
         wk     : Weakening 𝓔
         ⟦var⟧  : {Γ : Context} {σ : Type} → 𝓔 Γ σ → Γ ⊢ σ

module Fundamental {ℓ : Level} {𝓔 : Model ℓ} (𝓢 : Syntactic 𝓔) where

  open Syntactic 𝓢

  -- Using copatterns here guarantees that these things are not unfolded
  -- when normalising goals thus making them more readable.
  syntactic : Semantics 𝓔 _⊢_
  Semantics.wk     syntactic = wk
  Semantics.embed  syntactic = embed
  Semantics.⟦var⟧  syntactic = ⟦var⟧
  Semantics.⟦λ⟧    syntactic = λ t → `λ (t extend (lookup embed zero))
  Semantics._⟦$⟧_  syntactic = _`$_
  Semantics.⟦⟨⟩⟧   syntactic = `⟨⟩
  Semantics.⟦tt⟧   syntactic = `tt
  Semantics.⟦ff⟧   syntactic = `ff
  Semantics.⟦ifte⟧ syntactic = `ifte

  lemma : {Δ Γ : Context} {σ : Type} → Γ ⊢ σ → Var Γ ⇒[ 𝓔 ] Δ → Δ ⊢ σ
  lemma = Semantics.Fundamental.lemma syntactic
