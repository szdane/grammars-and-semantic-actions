open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.List (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet
open import Grammar.Maybe Alphabet
open import Monad Alphabet

private
  variable
    ℓg ℓh ℓk : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk

open Monad
open StrongMonad

module _ (g : Grammar ℓg) where
  data List : Grammar ℓg where
    nil : ⊤-grammar {ℓg} ⊢ List
    cons : g & List ⊢ List

  caseList :
    ⊤-grammar ⊢ h →
    g & List ⊢ h →
    List ⊢ h
  caseList e⊤ e& _ (nil _ x) = e⊤ _ x
  caseList e⊤ e& _ (cons _ x) = e& _ x

  ListElim :
    ⊤-grammar {ℓk} ⊢ k →
    g & k ⊢ k →
    List ⊢ k
  ListElim e e' _ (nil _ x) = e _ _
  ListElim e e' _ (cons _ x) =
    e' _ (x .fst , ListElim e e' _ (x .snd))

  ++List : List & List ⊢ List
  ++List =
    ⇒-intro⁻
      (ListElim {ℓg}
        (⇒-intro &-π₂)
        (⇒-intro
          (⇒-app ∘g
          &-swap ∘g
          &-par cons id ∘g
          &-assoc ∘g
          &-par id &-swap ∘g
          &-assoc⁻)))

filter :
  g ⊢ Maybe h →
  List g ⊢ List h
filter {g = g} f =
  ListElim g
    nil
    (⇒-intro⁻
      (⊕-elim
        (⇒-intro cons)
        id⇒) ∘g
    &-par f id)

ListMonad : Monad List
ListMonad .return = cons ∘g &-intro id (nil ∘g ⊤-intro)
ListMonad .μ {g = g} =
  ListElim (List g)
    nil
    (++List g)
ListMonad .fmap {g = g}{h = h} f =
  ListElim g {k = List h} nil (cons ∘g &-par f id)

open LeftStrongMonad
ListLeftStrongMonad : ∀ {ℓg} → LeftStrongMonad List
ListLeftStrongMonad .monad = ListMonad
ListLeftStrongMonad {ℓg} .leftStrength {g = g}{h = h} =
  ⊸-intro⁻
    (ListElim h {ℓk = ℓg}
      (⊸-intro (nil ∘g ⊤-intro))
      (⊸-intro (cons ∘g &-par id ⊸-app ∘g ⊗-dist-over-&)))
