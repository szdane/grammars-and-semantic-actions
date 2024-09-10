{-# OPTIONS --guardedness --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum

module Grammar.Search (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Grammar.Maybe Alphabet as Maybe using (Maybe)
open import Term Alphabet
open import Monad Alphabet

private
  variable
    ℓG ℓH : Level
    g : Grammar ℓG
    h : Grammar ℓH

record Search (g : Grammar ℓG) (w : String) : Type ℓG where
  coinductive
  constructor mkSearch
  field
    viewSearch :
      -- found one thing
      (g ⊕
      -- found nothing
      (⊤-grammar {ℓ-zero} ⊕
      -- split into two parallel searches
      ((Search g & Search g) ⊕
      -- delay
      Search g))) w

open Search

view : Search g ⊢ g ⊕ ⊤-grammar {ℓ-zero} ⊕ (Search g & Search g) ⊕ Search g
view _ = viewSearch

unfold :
  h ⊢ g ⊕ (⊤-grammar {ℓ-zero} ⊕ ((h & h) ⊕ h))
  → h ⊢ Search g
unfold f w x .viewSearch with f w x
... | inl pg = inl pg
... | inr (inl _) = inr (inl _)
... | inr (inr (inl (ph , ph'))) =
        inr (inr (inl ((unfold f _ ph) , unfold f _ ph')))
... | inr (inr (inr ph)) = inr (inr (inr (unfold f _ ph)))

search-fmap : g ⊢ h → Search g ⊢ Search h
search-fmap f =
  unfold
    (⊕-elim
      (⊕-inl ∘g f)
      (⊕-elim
        (⊕-inr ∘g ⊕-inl)
        (⊕-elim
          (⊕-inr ∘g ⊕-inr ∘g ⊕-inl)
          (⊕-inr ∘g ⊕-inr ∘g ⊕-inr))) ∘g view)

search-return : g ⊢ Search g
search-return = unfold ⊕-inl

nil : ⊤-grammar {ℓ-zero} ⊢ Search g
nil = unfold (⊕-inr ∘g ⊕-inl)

append : Search g & Search g ⊢ Search g
append w (pg , pg') = mkSearch (inr (inr (inl (pg , pg'))))

wait : Search g ⊢ Search g
wait = unfold (⊕-inr ∘g ⊕-inr ∘g ⊕-inr)

open Monad

SearchMonad : Monad Search
SearchMonad .return = search-return
SearchMonad .μ =
  unfold
    (⊕-elim
      (⊕-elim
        ⊕-inl
        (⊕-elim
          (⊕-inr ∘g ⊕-inl)
          (⊕-elim
            (⊕-inr ∘g ⊕-inr ∘g ⊕-inl ∘g
              &-par (SearchMonad .return) (SearchMonad .return))
            (⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g SearchMonad .return))) ∘g
      view)
      (⊕-elim
        (⊕-inr ∘g ⊕-inl)
        (⊕-elim
          (⊕-inr ∘g ⊕-inr ∘g ⊕-inl)
          (⊕-inr ∘g ⊕-inr ∘g ⊕-inr))) ∘g
    view)
SearchMonad .fmap f = search-fmap f

open LeftStrongMonad

SearchLeftStrongMonad : LeftStrongMonad Search
SearchLeftStrongMonad .monad = SearchMonad
SearchLeftStrongMonad .leftStrength =
  unfold
    (⊕-elim
      ⊕-inl 
      (⊕-elim
        (⊕-inr ∘g ⊕-inl ∘g ⊤-intro)
        (⊕-elim
          (⊕-inr ∘g ⊕-inr ∘g ⊕-inl ∘g ⊗&-distL ∘g ⊗-intro id (&-par view view))
          (⊕-inr ∘g ⊕-inr ∘g ⊕-inr ∘g ⊗-intro id view) ∘g
        ⊗⊕-distL) ∘g
      ⊗⊕-distL) ∘g
    ⊗⊕-distL) ∘g
  ⊗-intro id view

ext : g ⊢ Search h
  → Search g ⊢ Search h
ext {h = h} f = SearchMonad .μ ∘g SearchMonad .fmap f
