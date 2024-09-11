{-# OPTIONS --guardedness --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Parser (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.FinSet
open import Cubical.Data.List hiding (init)

open import Grammar Alphabet
open import Grammar.Search Alphabet as Search
open import Grammar.KleeneStar Alphabet
open import NFA.Base Alphabet
open import Term Alphabet
open import Monad Alphabet
open import Helper

private
  variable ℓN ℓN' ℓP ℓ : Level

module _ (N : NFA {ℓN}) where
  open NFA N
  open *r-Algebra
  open Monad
  open LeftStrongMonad

  run-ε : ε-grammar ⊢ LinΠ[ q ∈ ⟨ Q ⟩ ] Search (Parse q)
  run-ε =
    LinΠ-intro (λ q →
      append ∘g
      &-intro
        -- parses terminating at q
        (decRec
          (λ qAcc → SearchMonad .return ∘g Parse.nil qAcc)
          (λ _ → Search.nil ∘g ⊤-intro)
          (isAcc q .snd))
        -- parses resulting from a ε-cons out of q
        {!!}
    )

  runNFA : string-grammar ⊢ LinΠ[ q ∈ ⟨ Q ⟩ ] Search (Parse q)
  runNFA = foldKL*r char the-alg
    where
    the-alg : *r-Algebra char
    the-alg .the-ℓ = ℓN
    the-alg .G = LinΠ[ q ∈ ⟨ Q ⟩ ] Search (Parse q)
    the-alg .nil-case =
      LinΠ-intro
        (λ q →
          {!!}
          -- decRec
          --   (λ qAcc → SearchMonad .return ∘g Parse.nil qAcc)
          --   (λ _ → Search.nil ∘g ⊤-intro)
          --   (isAcc q .snd)
        )
    the-alg .cons-case =
      ⟜-intro⁻ (LinΣ-elim (λ c →
        ⟜-intro (LinΠ-intro {h = λ q' → Search (Parse q')}(λ q →
            -- TODO need a lemma that relates eliminating out of
            -- a linear pi over a finite type A to a search over
            -- elements of A that satisfy some predicate?
            -- Something that quantifies over all states, succeeds for
            -- those that have a c-labeled transition from q and fails
            -- on those that don't
            {!!} ∘g
            LinΠ-map (λ _ → SearchLeftStrongMonad .leftStrength) ∘g
            LinΠ-intro
            {h = λ q'' → literal c ⊗ Search (Parse q'')}
            (λ q' → ⊗-intro id (LinΠ-app q'))))))
