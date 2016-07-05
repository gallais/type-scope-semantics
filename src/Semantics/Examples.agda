module Semantics.Examples where

open import Syntax hiding (_∋_)
open import Syntax.Core.Examples
open import Semantics.Environment hiding (refl)

open import Function
open import Relation.Binary.PropositionalEquality

-- RENAMING & SUBSTITUTION

open import Semantics.Syntactic.Instances

substAPP : {σ : Type} → substitute APP (`ε `∙ FORCE `∙ (THUNK `$ ID))
         ≡ (ε ⊢ σ `→ σ ∋ ID')
substAPP = refl

-- PRINTING
open import Semantics.Printing

printID : {σ : Type} → print (ε ⊢ σ `→ σ ∋ ID) ≡ "λa. a"
printID = refl

printTRUE : {σ τ : Type} → print (ε ⊢ σ `→ τ `→ σ ∋ TRUE) ≡ "λa. λb. a"
printTRUE = refl

printFALSE : {σ τ : Type} → print (ε ⊢ σ `→ τ `→ τ ∋ FALSE) ≡ "λa. λb. b"
printFALSE = refl

printIFTE : {σ : Type} → print (ε ⊢ `Bool `→ (σ `→ σ `→ σ) ∋ IFTE)
          ≡ "λa. if (a) then (λb. λc. b) else (λd. λe. e)"
printIFTE = refl

printTHUNK : {σ τ : Type} → print (ε ⊢ σ `→ `Unit `→ σ ∋ THUNK) ≡ "λa. λb. a"
printTHUNK = refl

printFORCE : {σ τ : Type} → print (ε ⊢ (`Unit `→ σ) `→ σ ∋ FORCE) ≡ "λa. a (⟨⟩)"
printFORCE = refl

printID' : print (ε ⊢ `Bool `→ `Bool ∋ ID') ≡ "λa. a (⟨⟩) (λb. λc. b (λd. d))"
printID' = refl

-- NORMALISING
open import Semantics.NormalisationByEvaluation.βιξη

normID'Bool : norm' (ε ⊢ `Bool `→ `Bool ∋ ID') ≡ `λ (`neu _ (`var zero))
normID'Bool = refl

normID'Unit : norm' (ε ⊢ `Unit `→ `Unit ∋ ID') ≡ `λ `⟨⟩
normID'Unit = refl
