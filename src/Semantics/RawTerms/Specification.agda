module Semantics.RawTerms.Specification where

open import Data.Nat
open import Data.Fin
open import Syntax.Type
open import Syntax.RawTerms

record _─Env (m : ℕ) (𝓔 : ℕ → Set) (n : ℕ) : Set where
  field lookup : Fin m → 𝓔 n
open _─Env public

Renaming : (m n : ℕ) → Set
Renaming m n = (m ─Env) Fin n

extend : ∀ {n} → Renaming n (suc n)
lookup extend k = suc k

Kripke : (𝓔 𝓜 : ℕ → Set) → (ℕ → Set)
Kripke 𝓔 𝓜 m = ∀ {n} → Renaming m n → 𝓔 n → 𝓜 n

Weakening : (𝓔 : ℕ → Set) → Set
Weakening 𝓔 = ∀ {m n} → Renaming m n → 𝓔 m → 𝓔 n

_∙_ : ∀ {m n 𝓔} → (m ─Env) 𝓔 n → 𝓔 n → (suc m ─Env) 𝓔 n
lookup (ρ ∙ v) zero    = v
lookup (ρ ∙ v) (suc k) = lookup ρ k

wk^Env : ∀ {m 𝓔} → Weakening 𝓔 → Weakening ((m ─Env) 𝓔)
lookup (wk^Env wk ren ρ) k = wk ren (lookup ρ k)

record Semantics (𝓔 𝓜 : ℕ → Set) : Set where
  infixl 5 _⟦$⟧_
  field

    wk      :  Weakening 𝓔
    ⟦var⟧   :  {n : ℕ} → 𝓔 n → 𝓜 n
    ⟦λ⟧     :  {n : ℕ} (σ : Type) → Kripke 𝓔 𝓜 n → 𝓜 n
    _⟦$⟧_   :  {n : ℕ} → 𝓜 n → 𝓜 n → 𝓜 n
    ⟦⟨⟩⟧    :  {n : ℕ} → 𝓜 n
    ⟦tt⟧    :  {n : ℕ} → 𝓜 n
    ⟦ff⟧    :  {n : ℕ} → 𝓜 n
    ⟦ifte⟧  :  {n : ℕ} → 𝓜 n → 𝓜 n → 𝓜 n → 𝓜 n

module Eval {𝓔 𝓜} (𝓢 : Semantics 𝓔 𝓜) where

  open Semantics 𝓢

  sem : ∀ {m n} → (m ─Env) 𝓔 n → Raw m → 𝓜 n
  sem ρ (`var x)      = ⟦var⟧ (lookup ρ x)
  sem ρ (f `$ t)      = sem ρ f ⟦$⟧ sem ρ t
  sem ρ (`λ σ t)      = ⟦λ⟧ σ (λ ren v → sem (wk^Env wk ren ρ ∙ v) t)
  sem ρ `⟨⟩           = ⟦⟨⟩⟧
  sem ρ `tt           = ⟦tt⟧
  sem ρ `ff           = ⟦ff⟧
  sem ρ (`ifte b l r) = ⟦ifte⟧ (sem ρ b) (sem ρ l) (sem ρ r)
