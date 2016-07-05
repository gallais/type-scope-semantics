module Syntax.Normal.Weakening where

open import Syntax.Type
open import Syntax.Context
open import Syntax.Normal
open import Semantics.Environment as Env hiding (refl)
open import Semantics.Syntactic.Instances
open import Properties.Relation
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

mutual

  wk^ne : {R : Type → Set} → Weakening (_⊢[ R ]^ne_)
  wk^ne inc (`var v)        = `var (wk^∋ inc v)
  wk^ne inc (ne `$ u)       = wk^ne inc ne `$ wk^nf inc u
  wk^ne inc (`ifte ne l r)  = `ifte (wk^ne inc ne) (wk^nf inc l) (wk^nf inc r)

  wk^nf : {R : Type → Set} → Weakening (_⊢[ R ]^nf_)
  wk^nf inc (`neu pr t) = `neu pr (wk^ne inc t)
  wk^nf inc `⟨⟩         = `⟨⟩
  wk^nf inc `tt         = `tt
  wk^nf inc `ff         = `ff
  wk^nf inc (`λ nf)     = `λ (wk^nf (pop! inc) nf)

wk^whne : Weakening _⊢^whne_
wk^whne inc (`var v)        = `var (wk^∋ inc v)
wk^whne inc (ne `$ u)       = wk^whne inc ne `$ rename inc u
wk^whne inc (`ifte ne l r)  = `ifte (wk^whne inc ne) (rename inc l) (rename inc r)

wk^whnf : Weakening _⊢^whnf_
wk^whnf inc (`whne t)  = `whne (wk^whne inc t)
wk^whnf inc `⟨⟩        = `⟨⟩
wk^whnf inc `tt        = `tt
wk^whnf inc `ff        = `ff
wk^whnf inc (`λ b)     = `λ (rename (pop! inc) b)

mutual

  wk^nf-trans′ : 
    ∀ {Γ Δ Θ σ R inc₁ inc₃} {inc₂ : Renaming Δ Θ} →
    `∀[ Equality ] (Env.trans inc₁ inc₂) inc₃ →
    (t : Γ ⊢[ R ]^nf σ) → wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf inc₃ t
  wk^nf-trans′ eq (`neu pr t) = cong (`neu pr) $ wk^ne-trans′ eq t
  wk^nf-trans′ eq `⟨⟩         = refl
  wk^nf-trans′ eq `tt         = refl
  wk^nf-trans′ eq `ff         = refl
  wk^nf-trans′ eq (`λ t)      =
    cong `λ $ wk^nf-trans′ ((cong 1+_ ∘ lookup^R eq) ∙^R′ refl) t 

  wk^ne-trans′ : 
    ∀ {Γ Δ Θ σ R inc₁ inc₃} {inc₂ : Renaming Δ Θ} →
    `∀[ Equality ] (Env.trans inc₁ inc₂) inc₃ →
    (t : Γ ⊢[ R ]^ne σ) → wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne inc₃ t
  wk^ne-trans′ eq (`var v)      = cong `var $ lookup^R eq v
  wk^ne-trans′ eq (t `$ u)      = cong₂ _`$_ (wk^ne-trans′ eq t) (wk^nf-trans′ eq u)
  wk^ne-trans′ eq (`ifte t l r) =
    cong₂ (uncurry `ifte) (cong₂ _,_ (wk^ne-trans′ eq t) (wk^nf-trans′ eq l))
          (wk^nf-trans′ eq r)

wk^nf-trans :
  ∀ {Γ Δ Θ σ R inc₁} {inc₂ : Renaming Δ Θ} →
  (t : Γ ⊢[ R ]^nf σ) → wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf (Env.trans inc₁ inc₂) t  
wk^nf-trans = wk^nf-trans′ $ pack^R $ λ _ → refl

wk^ne-trans :
  ∀ {Γ Δ Θ σ R inc₁} {inc₂ : Renaming Δ Θ} →
  (t : Γ ⊢[ R ]^ne σ) → wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne (Env.trans inc₁ inc₂) t  
wk^ne-trans = wk^ne-trans′ $ pack^R $ λ _ → refl
