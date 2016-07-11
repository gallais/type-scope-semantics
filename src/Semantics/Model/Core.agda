module Semantics.Model.Core (Type : Set) where

open import Level
open import Syntax.Context

Model : (ℓ : Level) → Set (suc ℓ)
Model ℓ = Context Type → Type → Set ℓ

