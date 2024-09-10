open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Maybe (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet
open import Grammar.Exception Alphabet
open import Monad Alphabet

private
  variable
    ℓg ℓh ℓk : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk

Maybe : Grammar ℓg → Grammar ℓg
Maybe {ℓg = ℓg} g = g ⊕ ⊤-grammar {ℓ-zero}

just : g ⊢ Maybe g
just = ⊕-inl

nothing : h ⊢ Maybe g
nothing = ⊕-inr ∘g ⊤-intro

open Monad
open StrongMonad

MaybeMonad : Monad Maybe
MaybeMonad = ExceptionMonad ⊤-grammar

MaybeStrongMonad : StrongMonad Maybe
MaybeStrongMonad .monad = MaybeMonad
MaybeStrongMonad .leftStrength {g = g}{h = h} =
  ⊸-intro⁻
    (⊕-elim
      (⊸-intro just)
      (⊸-intro (nothing {g = g ⊗ h})))
MaybeStrongMonad .rightStrength {g = g}{h = h} =
  ⟜-intro⁻
    (⊕-elim
      (⟜-intro just)
      (⟜-intro (nothing {g = g ⊗ h})))
