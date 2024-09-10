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
append = {!!}

wait : Search g ⊢ Search g
wait = unfold (⊕-inr ∘g ⊕-inr ∘g ⊕-inr)

open Monad

SearchMonad : Monad Search
SearchMonad .return = search-return
SearchMonad .μ =
  {!!}
SearchMonad .fmap f = search-fmap f

-- This uses the old defs and might be wrong, but it type checks
-- open Monad
-- SearchMonad : Monad Search
-- SearchMonad .return = unfold (⊕-inr ∘g ⊕-inl ∘g &-intro id id)
-- SearchMonad .μ =
--   unfold
--     (⊕-elim
--       ⊕-inl
--       (⊕-elim
--         (⊕-elim
--           (⊕-inl ∘g &-π₁)
--           (⊕-elim
--             (⊕-inr ∘g ⊕-inl ∘g &-par &-π₁ id)
--             (⊕-inr ∘g ⊕-inr ∘g &-π₂) ∘g
--           &⊕-distR) ∘g
--         &⊕-distR ∘g
--         &-par view id)
--         (⊕-inr ∘g ⊕-inr))
--     ∘g view)
-- SearchMonad .fmap f =
--   unfold
--     (⊕-elim ⊕-inl (⊕-elim (⊕-inr ∘g ⊕-inl ∘g &-par f id) (⊕-inr ∘g ⊕-inr)) ∘g
--     view)

open LeftStrongMonad

SearchLeftStrongMonad : LeftStrongMonad Search
SearchLeftStrongMonad .monad = SearchMonad
SearchLeftStrongMonad .leftStrength =
  {!!}

ext : g ⊢ Search h
  → Search g ⊢ Search h
ext {h = h} f = SearchMonad .μ ∘g SearchMonad .fmap f
