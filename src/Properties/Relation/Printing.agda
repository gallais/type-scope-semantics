module Properties.Relation.Printing where

open import Semantics.Printing
open import Properties.Relation
open import Function
open import Relation.Binary.PropositionalEquality

_≈_ : RModel _ Printer Printer
_≈_ = mkRModel $ λ p q → ∀ {names names′} →
      names ≡ names′ → runPrinter p names ≡ runPrinter q names′
