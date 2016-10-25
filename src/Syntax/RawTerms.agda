module Syntax.RawTerms where

open import Data.Nat
open import Data.Fin
open import Syntax.Type

data Raw (n : ℕ) : Set where

  `var : Fin n →
         --------
         Raw n

  _`$_ : Raw n → Raw n →
         ---------------
         Raw n

  `λ   : Type → Raw (suc n) →
         --------------------
         Raw n

  `⟨⟩ `tt `ff :
         -------
         Raw n 
         
  `ifte : Raw n → Raw n → Raw n →
          -----------------------
          Raw n
