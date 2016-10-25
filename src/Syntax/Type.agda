module Syntax.Type where

open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

infixr 20 _`→_
data Type : Set where
  `Unit  : Type
  `Bool  : Type
  _`→_   : (σ τ : Type) → Type

`→-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ `→ τ₁ ≡ σ₂ `→ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`→-inj refl = refl , refl

isArrow : (σ : Type) → Dec (Σ[ στ ∈ Type × Type ] σ ≡ uncurry _`→_ στ)
isArrow `Unit    = no (λ { (_ , ()) })
isArrow `Bool    = no (λ { (_ , ()) })
isArrow (σ `→ τ) = yes ((σ , τ) , refl)

eqType : (σ τ : Type) → Dec (σ ≡ τ)
eqType `Unit      `Unit      = yes refl
eqType `Bool      `Bool      = yes refl
eqType (σ₁ `→ τ₁) (σ₂ `→ τ₂) with eqType σ₁ σ₂ | eqType τ₁ τ₂
... | yes p₁ | yes p₂ = yes (cong₂ _`→_ p₁ p₂)
... | no ¬p₁ | _      = no (¬p₁ ∘ proj₁ ∘ `→-inj)
... | _      | no ¬p₂ = no (¬p₂ ∘ proj₂ ∘ `→-inj)
eqType `Unit `Bool = no (λ ())
eqType `Unit (_ `→ _) = no (λ ())
eqType `Bool `Unit = no (λ ())
eqType `Bool (_ `→ _) = no (λ ())
eqType (_ `→ _) `Bool = no (λ ())
eqType (_ `→ _) `Unit = no (λ ())
