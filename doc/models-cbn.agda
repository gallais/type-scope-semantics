module models-cbn where

open import Level
open import Data.Unit
open import Function
open import models

module βιξη-cbn where

 
  open NormalForms βιξη.R public

  Kr : Model {Ty} zero
  Kr `1        = const ⊤
  Kr `2        = Nf `2
  Kr (σ `→ τ)  = □ (Kr σ) ⟶ Kr τ

  reify : ∀ σ → [ □ (Kr σ) ⟶ Nf σ ]
  reflect : ∀ σ → [ Ne σ ⟶ □ (Kr σ) ]

  reify `1        = const `⟨⟩
  reify `2        = _$ refl
  reify (σ `→ τ)  = λ {Γ} F →
    let var‿0 : ∀ {Δ} → Γ ∙ σ ⊆ Δ → □ (Kr σ) Δ
        var‿0 = λ inc ρ → reflect σ (`var (lookup (ρ [∘] inc) ze)) refl
    in `λ (reify τ (λ inc → F (inc [∘] step refl) (var‿0 inc)))

  reflect `1        = λ _ _ → tt
  reflect `2        = λ ne inc → `ne _ (th^ne _ inc ne)
  reflect (σ `→ τ)  = λ ne inc v →
    let body = (th^ne _ inc ne `$ reify σ v)
    in reflect τ body refl

  Normalise : Semantics (□ ∘ Kr) (□ ∘ Kr)
  Normalise = record
    { th    = λ _ → th^□
    ; ⟦var⟧ = id
    ; ⟦λ⟧   = λ b inc v → b inc v refl
    ; _⟦$⟧_ = λ f t inc → f inc (th^□ inc t)
    ; ⟦⟨⟩⟧  = const tt
    ; ⟦tt⟧  = const `tt
    ; ⟦ff⟧  = const `ff
    ; ⟦if⟧  = λ {σ} → if σ
    } module If where

      if : ∀ σ → [ □ (Kr `2) ⟶ □ (Kr σ) ⟶ □ (Kr σ) ⟶ □ (Kr σ) ]
      if σ b l r inc with b inc
      ... | `ne _ t = reflect σ (`if t (grab l) (grab r)) refl where
        grab = th^nf σ inc ∘ reify σ
      ... | `tt     = l inc
      ... | `ff     = r inc

  norm : ∀ σ → [ Tm σ ⟶ Nf σ ]
  norm σ t = reify σ (Eval.sem Normalise dummy t) where

    dummy : ∀ {Γ} → (Γ -Env) (□ ∘ Kr) Γ
    dummy = pack (λ {σ} v → reflect σ (`var v))
