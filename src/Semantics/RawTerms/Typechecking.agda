module Semantics.RawTerms.Typechecking where

open import Level
open import Data.Maybe as M
open import Data.Product
open import Function hiding (_∋_)

open import Syntax.Core hiding (_<$>_)
open import Syntax.RawTerms
open import Semantics.RawTerms.Specification
open import Semantics.Erasure

open import Category.Monad
open RawMonad (M.monad {Level.zero})

TYP : Semantics (const Type) (const $ Maybe Type)
Semantics.wk     TYP = const id
Semantics.⟦var⟧  TYP = just
Semantics.⟦λ⟧    TYP = λ σ b → M.map (σ `→_) (b extend σ)
Semantics._⟦$⟧_  TYP = λ f t → f                        >>= λ στ →
                               decToMaybe (isArrow στ)  >>= λ r → let ((σ , τ) , _) = r in
                               t                        >>= λ σ′ →
                               τ <$ decToMaybe (eqType σ σ′)
Semantics.⟦⟨⟩⟧   TYP = just `Unit
Semantics.⟦tt⟧   TYP = just `Bool
Semantics.⟦ff⟧   TYP = just `Bool
Semantics.⟦ifte⟧ TYP = λ b l r → b                           >>= λ β →
                                 decToMaybe (eqType β `Bool) >>= λ _ → 
                                 l                           >>= λ σ →
                                 r                           >>= λ τ →
                                 σ <$ decToMaybe (eqType σ τ)
