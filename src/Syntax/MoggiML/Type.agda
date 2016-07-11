module Syntax.MoggiML.Type where

open import Data.Product
open import Relation.Binary.PropositionalEquality

infixr 20 _`→_
data Type : Set where
  `Unit  : Type
  `Bool  : Type
  _`→_   : (σ τ : Type) → Type
  #_     : Type → Type

`→-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → (σ₁ `→ τ₁) ≡ (σ₂ `→ τ₂) → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`→-inj refl = refl , refl

#-inj : {σ τ : Type} → # σ ≡ # τ → σ ≡ τ
#-inj refl = refl
