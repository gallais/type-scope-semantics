module Syntax.Type where

infixr 20 _`→_
data Type : Set where
  `Unit  : Type
  `Bool  : Type
  _`→_   : (σ τ : Type) → Type
