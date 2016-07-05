module Semantics.Printing where

open import Syntax.Core
open import Semantics.Environment hiding (_<$>_)
open import Semantics.Specification

open import Function
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Char using (Char)
open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.List as List hiding (_++_ ; zipWith ; [_])
open import Coinduction
open import Data.Stream as Stream using (Stream ; head ; tail ; zipWith ; _∷_)
open import Category.Monad.State
open RawIMonadState (StateMonadState (Stream String)) hiding (zipWith ; pure)

record Name (Γ : Context) (σ : Type) : Set where
  constructor mkName
  field runName : String

record Printer (Γ : Context) (σ : Type) : Set where
  constructor mkPrinter
  field runPrinter : State (Stream String) String

open Name public
open Printer public

formatλ : String → String → String
formatλ x b = "λ" ++ x ++ ". " ++ b

format$ : String → String → String
format$ f t = f ++ " (" ++ t ++ ")"

formatIf : String → String → String → String
formatIf b l r = "if (" ++ b  ++ ") then (" ++ l ++ ") else (" ++ r ++ ")"

embed : {Γ : Context} → Var Γ ⇒[ Name ] Γ
lookup embed v = mkName (show (deBruijn v)) where

  deBruijn : {Γ : Context} {σ : Type} → σ ∈ Γ → ℕ
  deBruijn zero    = 0
  deBruijn (1+ n)  = 1 + deBruijn n

Printing : Semantics Name Printer
Printing = record
  { embed   = embed
  ; wk      = λ _ → mkName ∘ runName
  ; ⟦var⟧   = mkPrinter ∘ return ∘ runName
  ; _⟦$⟧_   =  λ mf mt → mkPrinter $ format$ <$> runPrinter mf ⊛ runPrinter mt
  ; ⟦λ⟧     =  λ {_} {σ} mb →
               mkPrinter $ get >>= λ names → let `x` = head names in
               put (tail names)                                  >>= λ _ →
               runPrinter (mb (step {σ = σ} refl) (mkName `x`))  >>= λ `b` →
               return $ formatλ `x` `b`
  ; ⟦⟨⟩⟧    = mkPrinter $ return "⟨⟩"
  ; ⟦tt⟧    = mkPrinter $ return "tt"
  ; ⟦ff⟧    = mkPrinter $ return "ff"
  ; ⟦ifte⟧  =  λ mb ml mr → mkPrinter $
               formatIf <$> runPrinter mb ⊛ runPrinter ml ⊛ runPrinter mr }


flatten : {A : Set} → Stream (A × List A) → Stream A
flatten ((a , as) ∷ aass) = go a as (♭ aass) where
  go : {A : Set} → A → List A → Stream (A × List A) → Stream A
  go a []        aass = a ∷ ♯ flatten aass
  go a (b ∷ as)  aass = a ∷ ♯ go b as aass
names : Stream String
names = flatten $ zipWith cons letters $ "" ∷ ♯ Stream.map show (allNatsFrom 0)
  where
    cons : (Char × List Char) → String → (String × List String)
    cons (c , cs) suffix = appendSuffix c , map appendSuffix cs where
      appendSuffix : Char → String
      appendSuffix c  = fromList (c ∷ []) ++ suffix

    letters = Stream.repeat $ 'a' , toList "bcdefghijklmnopqrstuvwxyz"

    allNatsFrom : ℕ → Stream ℕ
    allNatsFrom k = k ∷ ♯ allNatsFrom (1 + k)

name : {Γ : Context} {σ : Type} → State (Stream String) (Name Γ σ)
name = get >>= λ names →
       put (tail names) >>
       return (mkName $ head names)

init : (Γ Δ : Context) → State (Stream String) (Var Γ ⇒[ Name ] Δ)
init ε       Δ = return `ε
init (Γ ∙ σ) Δ = (_`∙_ <$> init Γ Δ) ⊛ name

init' : {Γ : Context} → State (Stream String) (Var Γ ⇒[ Name ] Γ)
init' = init _ _

printer : Evaluation Name Printer
printer = Fundamental.lemma Printing

printer' : Evaluation' Printer
printer' = Fundamental.lemma' Printing

print : {Γ : Context} {σ : Type} → Γ ⊢ σ → String
print t =
  let printer = Fundamental.lemma Printing t
  in proj₁ $ init' >>= runPrinter ∘ printer $ names
