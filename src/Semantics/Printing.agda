module Semantics.Printing where

open import Syntax.Core hiding (_<$>_)
open import Semantics.Environment hiding (_<$>_)
open import Semantics.Specification

open import Function
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Char using (Char)
open import Data.String hiding (show)
open import Data.Nat.Show as NatShow
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)

open import Codata.Thunk
open import Codata.Stream as Stream using (Stream ; head ; tail ; zipWith ; _∷_)
open import Category.Monad.State
open RawIMonadState (StateMonadState (Stream String _)) hiding (zipWith ; pure)

M : Set → Set
M = State (Stream String _)

record Name (Γ : Context) (σ : Type) : Set where
  constructor mkName
  field runName : String

record Printer (Γ : Context) (σ : Type) : Set where
  constructor mkPrinter
  field runPrinter : M String

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


alphabetWithSuffix : String → List⁺ String
alphabetWithSuffix suffix = List⁺.map (λ c → fromList (c ∷ []) ++ suffix)
                          $′ 'a' ∷ toList "bcdefghijklmnopqrstuvwxyz"

allNats : Stream ℕ _
allNats = Stream.unfold < id , suc > 0

names : Stream String _
names = Stream.concat
      $′ Stream.map alphabetWithSuffix
      $′ "" ∷ λ where .force → Stream.map NatShow.show allNats

name : {Γ : Context} {σ : Type} → M (Name Γ σ)
name = do
  names ← get
  put (tail names)
  return (mkName $ head names)

init : (Γ Δ : Context) → M (Var Γ ⇒[ Name ] Δ)
init ε       Δ = return `ε
init (Γ ∙ σ) Δ = (_`∙_ <$> init Γ Δ) ⊛ name

init' : {Γ : Context} → M (Var Γ ⇒[ Name ] Γ)
init' = init _ _

printer : Evaluation Name Printer
printer = Fundamental.lemma Printing

printer' : Evaluation' Printer
printer' = Fundamental.lemma' Printing

print : {Γ : Context} {σ : Type} → Γ ⊢ σ → String
print t =
  let printer = Fundamental.lemma Printing t
  in proj₁ $ init' >>= runPrinter ∘ printer $ names
