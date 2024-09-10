{-# OPTIONS --guardedness --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet

module Parser (Alphabet : hSet ℓ-zero)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.List

open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.Maybe Alphabet
open import Grammar.Exception Alphabet
open import Grammar.List Alphabet as ListG
open import Grammar.Search Alphabet as Search
open import Term Alphabet
open import Monad Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

open Monad
open StrongMonad
open LeftStrongMonad

Parser : Grammar ℓg → Type ℓg
Parser g = string-grammar ⊢ Search (g ⊗ string-grammar)

⊤→string : ⊤-grammar {ℓ-zero} ⊢ string-grammar
⊤→string w _ = ⌈ w ⌉

_then_ : ∀ {g : Grammar ℓg} {h : Grammar ℓh} →
  Parser g → Parser h → Parser (g ⊗ h)
e then e' =
  ext
    (SearchMonad .fmap ⊗-assoc ∘g
    SearchLeftStrongMonad .leftStrength ∘g
    ⊗-intro id e') ∘g
  e

_or_ : Parser g → Parser g → Parser g
e or e' =
  ⊕-elim
    (SearchMonad .return)
    (⊕-elim (e' ∘g ⊤→string)
      (⊕-elim
        append
        wait)) ∘g
  view ∘g
  e

parseε : Parser ε-grammar
parseε = SearchMonad .return ∘g ⊗-unit-l⁻

parseChar : (c : ⟨ Alphabet ⟩) → Parser (literal c)
parseChar c =
  caseKL* char
    (Search.nil ∘g ⊤-intro)
    (⟜-intro⁻ (LinΣ-elim (λ c' →
      ⟜-intro
        (decRec
          (λ c'≡c →
            SearchMonad .return ∘g ⊗-intro (SubstTerm (cong literal c'≡c)) id)
          (λ _ → Search.nil ∘g ⊤-intro)
          (isFinSet→Discrete isFinSetAlphabet c' c)))))
